using KatLang.Tests.AsyncEvaluation;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using static KatLang.Tests.EvaluatorTestSupport;

namespace KatLang.Tests;

/// <summary>
/// SELECTION IS A VALUE BOUNDARY, NOT AN IMPLICIT SPREAD BOUNDARY.
///
/// <para><c>A:i</c>, <c>first(A)</c>, and <c>last(A)</c> CHOOSE a value: the selected
/// element is returned exactly as stored and re-counted through the ordinary value
/// boundary (<c>Result.valueCount</c>) — <c>()</c> emits zero values, everything else
/// (a sequence value, an exact list, a scalar) emits ONE. The selected value's origin is
/// forgotten, so every count-sensitive consumer (a lone root row, a collecting dotted
/// receiver, a loop-step output row, the map/reduce single-element checks, a
/// callback parameter) sees exactly what it would see for a property holding the same
/// value. A selection passed unspread is ONE written slot, so a collecting parameter
/// applies the collector supply-boundary law to it exactly as to <c>Coll(V)</c>: a lone
/// selected SEQUENCE value opens one level, a selected list, scalar, or a value beside
/// another slot is collected exactly (<c>CollectorSupplyBoundaryTests</c>). The spread
/// marker <c>*</c> OPENS a selected sequence or list — one boundary, per the ordinary
/// spread law.</para>
///
/// <para>Lean: <c>Result.select?</c> + the <c>.index</c> arm of <c>evalCounted</c>,
/// <c>evalFirstCounted</c>/<c>evalLastCounted</c>, <c>countedSequenceCallbackItem</c>
/// (all through <c>Result.valueCount</c>); the laws <c>select_is_a_value_boundary</c>,
/// <c>first_is_select_zero</c>, <c>last_is_select_last</c>, and
/// <c>callback_item_is_a_value_boundary</c> in <c>lean/KatLangArityLaws.lean</c>;
/// CoreTests <c>SelectionValueBoundary</c> guards.</para>
/// </summary>
public class SelectionValueBoundaryTests
{
    private const string Coll = "Coll(*xs) = xs\n";

    /// <summary>
    /// The semantic table of the rule: one representative per selected-value kind, with
    /// the collecting-receiver observation of the bare selection and of its explicit
    /// spread. <c>selection.Coll</c> is <c>Coll(selection)</c> — one written slot at a
    /// lone collector — so the middle column is decided by the collector supply-boundary
    /// law exactly as for <c>Coll(V)</c>: a selected SEQUENCE value opens one level
    /// (<c>()</c> to nothing, <c>(1, 2)</c> to <c>[1, 2]</c>, <c>((1, 2), 3)</c> to
    /// <c>[(1, 2), 3]</c> — never recursively), while a selected list, string, number, or
    /// Boolean is one exact collected item. <c>()</c> and <c>[]</c> are deliberately
    /// distinct rows: an empty SEQUENCE value emits zero values at a value boundary (so it
    /// spreads to nothing and opens to nothing) while an empty LIST is one exact value
    /// (<c>[].Coll</c> is <c>[[]]</c>, <c>[]*.Coll</c> is <c>[]</c>).
    /// </summary>
    public static TheoryData<string, string, string> SelectedValueTable => new()
    {
        // selected value   selection.Coll      (selection)*.Coll
        { "()",             "[]",               "[]" },
        { "1",              "[1]",              "[1]" },
        { "'s'",            "[s]",              "[s]" },
        { "true",           "[true]",           "[true]" },
        { "(1, 2)",         "[1, 2]",           "[1, 2]" },
        { "[]",             "[[]]",             "[]" },
        { "[1, 2]",         "[[1, 2]]",         "[1, 2]" },
        { "[()]",           "[[()]]",           "[()]" },
        { "[(1, 2)]",       "[[(1, 2)]]",       "[(1, 2)]" },
        { "((1, 2), 3)",    "[(1, 2), 3]",      "[(1, 2), 3]" },
        { "([1, 2], 3)",    "[[1, 2], 3]",      "[[1, 2], 3]" },
        { "((), 3)",        "[(), 3]",          "[(), 3]" },
    };

    /// <summary>
    /// Every selection spelling of the SAME element, each paired with the collection
    /// definition that places the element where the spelling selects it. The
    /// <c>{0}</c> placeholder receives the selected value.
    /// </summary>
    private static readonly (string Name, string Definition, string Selection)[] SelectionForms =
    [
        ("A:0", "A = ({0}, 9)\n", "A:0"),
        ("first(A)", "A = ({0}, 9)\n", "first(A)"),
        ("A:1", "A = (9, {0})\n", "A:1"),
        ("last(A)", "A = (9, {0})\n", "last(A)"),
        ("A:(A.count - 1)", "A = (9, {0})\n", "A:(A.count - 1)"),
        ("list A:0", "A = [{0}, 9]\n", "A:0"),
        ("list first(A)", "A = [{0}, 9]\n", "first(A)"),
        ("list last(A)", "A = [9, {0}]\n", "last(A)"),
    ];

    private static string Display(string source)
    {
        var run = KatLangEngine.Run(source);
        var success = Assert.IsType<RunResult.Success>(run);
        return success.ToDisplayString();
    }

    private static RunResult.Success Success(string source)
        => Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));

    private static string Neutral(string source)
        => SemanticExplorerHarness.Observe("selection", source).Neutral;

    // ── The semantic table through the collecting dotted receiver ────────────

    [Theory]
    [MemberData(nameof(SelectedValueTable))]
    public void EverySelectionForm_KeepsTheSelectedValueWhole_AndSpreadOpensIt(
        string selected, string expectedColl, string expectedSpreadColl)
    {
        foreach (var (name, definition, selection) in SelectionForms)
        {
            var defs = Coll + string.Format(definition, selected);
            Assert.Equal(expectedColl, Display(defs + selection + ".Coll"));
            Assert.Equal(expectedSpreadColl, Display(defs + "(" + selection + ")*.Coll"));

            // Fluent spread receiver spelling: `selection*.Coll` is `Coll(selection*)`.
            Assert.Equal(expectedSpreadColl, Display(defs + selection + "*.Coll"));

            // The direct call passes the selected value as ONE written slot — the very
            // same slot the dotted spelling supplies (dot-call passes a value: `R.Coll`
            // is `Coll(R)` for every receiver, `()` included) — and the same slot a
            // property holding the value supplies, so the collector supply-boundary law
            // decides all three alike.
            Assert.Equal(expectedColl, Display(defs + "Coll(" + selection + ")"));
            Assert.Equal(expectedColl, Display(defs + "V = " + selected + "\nColl(V)"));

            // Beside another written slot the selected value is collected EXACTLY,
            // whatever it is: the law rewrites only a segment that is ONE lone written
            // sequence value. The dotted spelling is the same call.
            var beside = Display("[" + selected + ", 9]");
            Assert.Equal(beside, Display(defs + "Coll(" + selection + ", 9)"));
            Assert.Equal(beside, Display(defs + selection + ".Coll(9)"));
        }
    }

    // ── Origin independence ─────────────────────────────────────────────────

    [Theory]
    [MemberData(nameof(SelectedValueTable))]
    public void StoredSelection_BehavesExactlyLikeTheBareSelection(
        string selected, string expectedColl, string expectedSpreadColl)
    {
        foreach (var (_, definition, selection) in SelectionForms)
        {
            var defs = Coll + string.Format(definition, selected) + "X = " + selection + "\n";
            Assert.Equal(expectedColl, Display(defs + "X.Coll"));
            Assert.Equal(expectedSpreadColl, Display(defs + "X*.Coll"));

            // Redundant parentheses are pure grouping (the parser erases them —
            // `Parser.IsRedundantGrouping`: parentheses group syntax), so the grouped
            // selection is the bare selection and the grouped NAME `(X)` is `X`.
            Assert.Equal(expectedColl, Display(defs + "(" + selection + ").Coll"));
            Assert.Equal(expectedColl, Display(defs + "(X).Coll"));
            Assert.Equal(expectedColl, Display(defs + "((X)).Coll"));

            // Passing the selected value through another ordinary value boundary
            // (a call) changes nothing.
            Assert.Equal(expectedColl, Display(defs + "Id(v) = v\nId(" + selection + ").Coll"));

            // A written brace receiver is one value (dot-call passes a value), so the
            // selection row and the literal row agree — and both are the one item.
            Assert.Equal(expectedColl, Display(defs + "{" + selection + "}.Coll"));
            Assert.Equal(expectedColl, Display(defs + "{" + selected + "}.Coll"));
        }
    }

    [Fact]
    public void EmptySequence_SelectedThroughAnyRoute_IsPlainEmpty()
    {
        // The motivating examples: `()` selected from a sequence, read from a property,
        // returned by a call, or chosen by `if` is simply `()` — one written slot when
        // passed (dot-call passes a value: `().Coll` is `Coll(())`), whose lone empty
        // sequence the collector opens to zero items exactly like the spread, while
        // beside another argument it stays ONE visible collected item. No route preserves
        // "one element was selected", and no route turns the value-boundary count 0 into
        // a missing argument (`One(a) = 1` accepts every one of them).
        const string defs = Coll + "A = ((), 1)\nE = ()\nFz(x) = ()\nB = (1, ())\nOne(a) = 1\n";
        foreach (var program in new[]
        {
            "A:0.Coll", "first(A).Coll", "B:1.Coll", "last(B).Coll",
            "E.Coll", "Fz(1).Coll", "if(true, (), 1).Coll", "().Coll",
            "Coll(A:0)", "Coll(first(A))", "Coll(E)", "Coll(Fz(1))", "Coll(())",
            "X = A:0\nX.Coll", "Y = first(A)\nY.Coll", "Z = last(B)\nZ.Coll",
        })
        {
            Assert.Equal("[]", Display(defs + program));
        }

        foreach (var program in new[]
        {
            "A:0.Coll(1)", "first(A).Coll(1)", "E.Coll(1)", "Fz(1).Coll(1)", "().Coll(1)",
            "Coll(A:0, 1)", "Coll(E, 1)", "Coll((), 1)", "X = A:0\nColl(X, 1)",
        })
        {
            Assert.Equal("[(), 1]", Display(defs + program));
        }

        foreach (var program in new[] { "One(A:0)", "One(E)", "One(())", "A:0.One", "E.One" })
        {
            Assert.Equal("1", Display(defs + program));
        }

        foreach (var program in new[]
        {
            "(A:0)*.Coll", "(first(A))*.Coll", "(last(B))*.Coll", "A:0*.Coll",
            "E*.Coll", "Fz(1)*.Coll", "()*.Coll",
            "Coll((A:0)*)", "Coll(E*)", "Coll(()*)",
        })
        {
            Assert.Equal("[]", Display(defs + program));
        }
    }

    [Fact]
    public void EmptyList_SelectedThroughAnyRoute_StaysOneExactList()
    {
        const string defs = Coll + "A = ([], 1)\nL = []\nFl(x) = []\nB = (1, [])\n";
        foreach (var program in new[]
        {
            "A:0.Coll", "first(A).Coll", "B:1.Coll", "last(B).Coll",
            "L.Coll", "Fl(1).Coll", "if(true, [], 1).Coll",
            "X = A:0\nX.Coll", "Y = last(B)\nY.Coll",
        })
        {
            Assert.Equal("[[]]", Display(defs + program));
        }

        foreach (var program in new[] { "(A:0)*.Coll", "(first(A))*.Coll", "(last(B))*.Coll", "L*.Coll" })
            Assert.Equal("[]", Display(defs + program));
    }

    // ── Count-sensitive observers ────────────────────────────────────────────

    [Theory]
    [MemberData(nameof(SelectedValueTable))]
    public void LoneRootRow_ShowsTheSelectedValueAsOneRow(
        string selected, string expectedColl, string expectedSpreadColl)
    {
        _ = expectedColl;
        _ = expectedSpreadColl;
        var literal = Success(selected);
        var literalDisplay = literal.ToDisplayString();

        foreach (var (_, definition, selection) in SelectionForms)
        {
            var success = Success(string.Format(definition, selected) + selection);

            // A non-spread root row is always one visible slot (the documented root
            // bump keeps a selected `()` visible), and the selected value is never
            // opened into several rows.
            Assert.Equal(literal.EmittedCount, success.EmittedCount);
            Assert.Equal(1, success.OutputRows.Count);
            Assert.True(Result.ValueComparer.Equals(literal.Value, success.Value));
            Assert.Equal(literalDisplay, success.ToDisplayString());
        }
    }

    [Theory]
    [MemberData(nameof(SelectedValueTable))]
    public void WrittenSlots_ReifyTheSelectionAsOneValue(
        string selected, string expectedColl, string expectedSpreadColl)
    {
        _ = expectedColl;
        _ = expectedSpreadColl;
        var expectedList = Display("[" + selected + ", 9]");
        var expectedSequence = Display("(" + selected + ", 9)");
        foreach (var (_, definition, selection) in SelectionForms)
        {
            var defs = string.Format(definition, selected);
            Assert.Equal(expectedList, Display(defs + "[" + selection + ", 9]"));
            Assert.Equal(expectedSequence, Display(defs + "(" + selection + ", 9)"));
            Assert.Equal("true", Display(defs + selection + " == " + selected));
        }
    }

    [Theory]
    [MemberData(nameof(SelectedValueTable))]
    public void LoopStepOutputRow_KeepsTheSelectionAsOneStateSlot(
        string selected, string expectedColl, string expectedSpreadColl)
    {
        _ = expectedColl;
        _ = expectedSpreadColl;
        var literalValue = Success(selected).Value;

        foreach (var (_, definition, selection) in SelectionForms)
        {
            var source = string.Format(definition, selected) + "S(x, y) = " + selection + ", y + 1\nrepeat(S, 1, 0, 0)";
            foreach (var optimize in new[] { false, true })
            {
                var result = EvalFull(source, optimize);
                if (result.IsError)
                    Assert.Fail($"Expected success ({(optimize ? "planned" : "generic")}) but got error: {result.Error}");

                // Two state slots: the selected value (never opened, never dropped)
                // and the counter.
                var state = Assert.IsType<Result.SequenceValue>(result.Value);
                Assert.Equal(2, state.Items.Count);
                Assert.True(Result.ValueComparer.Equals(literalValue, state.Items[0]));
                Assert.True(Result.ValueComparer.Equals(new Result.Atom(1), state.Items[1]));
            }
        }
    }

    [Theory]
    [MemberData(nameof(SelectedValueTable))]
    public void MapTransform_AndReduceStep_SeeTheSelectionAsOneValue(
        string selected, string expectedColl, string expectedSpreadColl)
    {
        _ = expectedColl;
        _ = expectedSpreadColl;
        // The literal route is the oracle: a transform returning the written value
        // (a capture / literal, count valueCount) — `()` is the documented empty
        // transform rejection, every other value is one mapped element.
        var literalMap = KatLangEngine.Run("H(x) = " + selected + "\nmap((1), H)");
        var literalReduce = KatLangEngine.Run("H(x, acc) = " + selected + "\nreduce((1), H, 0)");

        foreach (var (_, definition, selection) in SelectionForms)
        {
            var defs = string.Format(definition, selected);
            AssertSameOutcome(literalMap, KatLangEngine.Run(defs + "F(x) = " + selection + "\nmap((1), F)"));
            AssertSameOutcome(literalReduce, KatLangEngine.Run(defs + "F(x, acc) = " + selection + "\nreduce((1), F, 0)"));
        }
    }

    [Theory]
    [MemberData(nameof(SelectedValueTable))]
    public void CallbackItem_IsASelectedValue_WithTheSameBoundary(
        string selected, string expectedColl, string expectedSpreadColl)
    {
        // The iterated item of map/filter/reduce is a selection from the collection:
        // inside the callback it is ONE value on every count-sensitive path (a
        // collecting dotted receiver, a bare output row, the single-element checks),
        // and only an explicit spread opens it.
        var defs = Coll + "A = (" + selected + ", 9)\nF(x) = x.Coll\nG(x) = (x)*.Coll\nId(x) = x\nR(x, acc) = x\n";
        Assert.Equal("[" + expectedColl + ", [9]]", Display(defs + "map(A, F)"));
        Assert.Equal("[" + expectedSpreadColl + ", [9]]", Display(defs + "map(A, G)"));

        // A reduce step returning the selected item: one accumulator value, except
        // that `()` is the documented empty-accumulator rejection whatever produced it.
        var reduced = KatLangEngine.Run(defs + "reduce(A, R, 0)");
        if (selected == "()")
        {
            var reduceFailure = Assert.IsType<RunResult.EvalFailure>(reduced);
            Assert.Equal(KatLangErrorCode.ArityMismatch, Assert.Single(reduceFailure.Errors).Code);
            Assert.Contains("reduce step must return a single accumulator value", Assert.Single(reduceFailure.Errors).Message);
        }
        else
        {
            Assert.Equal("9", Assert.IsType<RunResult.Success>(reduced).ToDisplayString());
        }

        var identity = KatLangEngine.Run(defs + "map(A, Id)");
        if (selected == "()")
        {
            // `()` is the documented empty transform result, whatever produced it.
            var failure = Assert.IsType<RunResult.EvalFailure>(identity);
            Assert.Equal(KatLangErrorCode.ArityMismatch, Assert.Single(failure.Errors).Code);
            Assert.Contains("map transform must return a single element", Assert.Single(failure.Errors).Message);
        }
        else
        {
            // The identity transform maps each selected item to itself: one element
            // per item, nested values intact (`Id(x) = x` and `Wrap(x) = (x)` agree).
            Assert.Equal(Display("[" + selected + ", 9]"), Display(defs + "map(A, Id)"));
            Assert.Equal(Display("[" + selected + ", 9]"), Display(defs + "Wrap(x) = (x)\nmap(A, Wrap)"));
        }
    }

    // ── first / last ≡ index metamorphic invariant ───────────────────────────

    public static TheoryData<string> Collections => new()
    {
        "(1, 2)", "(7)", "(1, 2, 3)",
        "((), 1)", "(1, ())", "((), ())",
        "((1, 2), 3)", "(3, (1, 2))", "((1, 2), (3, 4))",
        "([], 1)", "(1, [])", "([1, 2], 3)", "(3, [1, 2])",
        "([()], [(1, 2)])", "(((1, 2), 3), ([1, 2], 3))",
        "[1, 2]", "[[]]", "[[1, 2], [3, 4]]", "[(1, 2), (3, 4)]", "[()]", "[[()]]",
        "((1, 2), (), [3])",
        "'text'", "7", "true",
    };

    [Theory]
    [MemberData(nameof(Collections))]
    public void First_IsSelectionAtZero_AndLast_IsSelectionAtCountMinusOne(string collection)
    {
        var defs = Coll + "A = " + collection + "\n";

        // Value + emitted count (neutral encoding), through every observer that can
        // see a live count, in the generic and the planned strategy, and through
        // the async twin.
        foreach (var (firstForm, lastForm) in new[]
        {
            ("first(A)", "last(A)"),
            ("first(A).Coll", "last(A).Coll"),
            ("(first(A))*.Coll", "(last(A))*.Coll"),
            ("first(A)*.Coll", "last(A)*.Coll"),
            ("[first(A), 9]", "[last(A), 9]"),
            ("S(x, y) = first(A), y + 1\nrepeat(S, 1, 0, 0)", "S(x, y) = last(A), y + 1\nrepeat(S, 1, 0, 0)"),
            ("F(x) = first(A)\nmap((1), F)", "F(x) = last(A)\nmap((1), F)"),
            ("X = first(A)\nX.Coll", "X = last(A)\nX.Coll"),
        })
        {
            var indexZero = firstForm.Replace("first(A)", "A:0");
            var indexLast = lastForm.Replace("last(A)", "A:(A.count - 1)");

            Assert.Equal(Neutral(defs + indexZero), Neutral(defs + firstForm));
            Assert.Equal(Neutral(defs + indexLast), Neutral(defs + lastForm));
            AssertLoopModesAndAsyncTwinAgree(defs + firstForm);
            AssertLoopModesAndAsyncTwinAgree(defs + lastForm);
        }
    }

    [Fact]
    public void SelectionFromAnEmptyCollection_FailsInEveryForm()
    {
        // The equivalence is stated for VALID selections; an empty target has none.
        // (`first`/`last` report the collection arity rejection and `:` the index
        // rejection — both are evaluation errors, pinned by kind.)
        foreach (var target in new[] { "()", "[]" })
        {
            var defs = "A = " + target + "\n";
            Assert.IsType<EvalError.BadArity>(Innermost(EvalFull(defs + "first(A)").Error));
            Assert.IsType<EvalError.BadArity>(Innermost(EvalFull(defs + "last(A)").Error));
            Assert.IsType<EvalError.BadIndex>(Innermost(EvalFull(defs + "A:0").Error));
        }
    }

    // ── Explicit spread still opens exactly one boundary ────────────────────

    [Fact]
    public void SpreadOfASelection_OpensExactlyOneBoundary()
    {
        const string defs = Coll + "A = (((1, 2), [3, 4]), 9)\nL = ([[1], [2, 3]], 9)\n";

        // One boundary: the selected sequence opens to its immediate items, which stay intact.
        Assert.Equal("[(1, 2), [3, 4]]", Display(defs + "(A:0)*.Coll"));
        Assert.Equal("[(1, 2), [3, 4]]", Display(defs + "(first(A))*.Coll"));
        Assert.Equal("[[1], [2, 3]]", Display(defs + "(L:0)*.Coll"));
        Assert.Equal("[[1], [2, 3]]", Display(defs + "(first(L))*.Coll"));

        // `value**` is `(value*)*`: the second star spreads each already-spread item
        // supply's single value again, never a recursive flattening.
        AssertEvalCounted(defs + "(A:0)*", 2, SequenceValue(SequenceValue(Atom(1), Atom(2)), ListValue(Atom(3), Atom(4))));
        AssertEvalCounted(defs + "(first(A))*", 2, SequenceValue(SequenceValue(Atom(1), Atom(2)), ListValue(Atom(3), Atom(4))));
        AssertEvalCounted(defs + "A:0*", 2, SequenceValue(SequenceValue(Atom(1), Atom(2)), ListValue(Atom(3), Atom(4))));

        // Selection then spread differs from spread then selection.
        Assert.Equal("[1, 2]", Display(defs + "B = [[1, 2], [3, 4]]\n(B:0)*.Coll"));
        Assert.Equal("[[1, 2]]", Display(defs + "B = [[1, 2], [3, 4]]\n(B*):0.Coll"));
    }

    [Fact]
    public void SelectionInsideNestedStructures_IsOneValue()
    {
        const string defs = Coll + "Bags = ((1, 2), (3, 4)), ((5, 6), (7, 8))\n";
        // Beside another written argument the selection is ONE exact collected item.
        Assert.Equal("[((1, 2), (3, 4)), 9]", Display(defs + "Coll(Bags:0, 9)"));
        Assert.Equal("[((1, 2), (3, 4)), 9]", Display(defs + "first(Bags).Coll(9)"));
        Assert.Equal("[(3, 4), 9]", Display(defs + "Coll(Bags:0:1, 9)"));
        Assert.Equal("[(3, 4), 9]", Display(defs + "last(first(Bags)).Coll(9)"));
        // Alone at the collector the selected sequence opens exactly one level — the
        // nested pairs stay intact — exactly as its spread supplies them.
        Assert.Equal("[(1, 2), (3, 4)]", Display(defs + "Bags:0.Coll"));
        Assert.Equal("[(1, 2), (3, 4)]", Display(defs + "first(Bags).Coll"));
        Assert.Equal("[3, 4]", Display(defs + "Bags:0:1.Coll"));
        Assert.Equal("[3, 4]", Display(defs + "last(first(Bags)).Coll"));
        Assert.Equal("[(1, 2), (3, 4)]", Display(defs + "(Bags:0)*.Coll"));
        Assert.Equal("[3, 4]", Display(defs + "(Bags:0:1)*.Coll"));
        Assert.Equal("[3, 4]", Display(defs + "(last(first(Bags)))*.Coll"));

        // A lone root row shows the intact selection, chained or not.
        Assert.Equal("((1, 2), (3, 4))", Display("Bags = ((1, 2), (3, 4)), ((5, 6), (7, 8))\nBags:0"));
        Assert.Equal("(3, 4)", Display("Bags = ((1, 2), (3, 4)), ((5, 6), (7, 8))\nBags:0:1"));
    }

    [Theory]
    [InlineData("()", "[]")]
    [InlineData("(1, 2)", "[1, 2]")]
    [InlineData("((1, 2), 3)", "[(1, 2), 3]")]
    [InlineData("[]", "[[]]")]
    [InlineData("[1, 2]", "[[1, 2]]")]
    [InlineData("[()]", "[[()]]")]
    [InlineData("[(1, 2)]", "[[(1, 2)]]")]
    public async Task CallbackBindingAndStorage_AgreeWithDirectCalls_IncludingFusedFilter(
        string selected, string collected)
    {
        var defs = Coll + "V = " + selected + "\nA = [V]\n";
        foreach (var callback in new[]
        {
            "F(x) = x.Coll\n",
            "F(x) = { X = x\nX.Coll }\n",
            "F(999) = [999]\nF(x) = x.Coll\n",
        })
        {
            await AssertExecutionPaths(defs + callback + "F(V)", collected);
            await AssertExecutionPaths(defs + callback + "map(A, F)", "[" + collected + "]");
        }

        await AssertExecutionPaths(defs + "R(x, acc) = x.Coll\nreduce(A, R, 0)", collected);
        await AssertExecutionPaths(defs + "R(x, acc) = { X = x\nX.Coll }\nreduce(A, R, 0)", collected);

        var filterDefs = defs + "Keep(x) = x.Coll == " + collected + "\n";
        await AssertExecutionPaths(filterDefs + "A.filter(Keep)", "[" + selected + "]");
        var (_, fusion) = await AssertExecutionPaths(filterDefs + "A.filter(Keep).count", "1");
        Assert.Equal(1, fusion.FilterCountFusionHits);
        Assert.Equal(1, fusion.FilterCountPredicateCalls);
    }

    [Theory]
    [InlineData("()", 0)]
    [InlineData("1", 1)]
    [InlineData("(1, 2)", 1)]
    [InlineData("[]", 1)]
    [InlineData("[1, 2]", 1)]
    [InlineData("[(1, 2)]", 1)]
    public async Task SelectionCount_IsMaterializedBeforeAnyRootRowDecoration(string selected, int count)
    {
        var expectedValue = Success(selected).Value;
        foreach (var expression in new[] { "[" + selected + "]:0", "first([" + selected + "])", "last([" + selected + "])" })
        {
            // Evaluate the expression itself: a root row would make even a zero-count
            // empty sequence visible and could hide a broken selection count.
            var expr = Assert.Single(ParseValidRoot(expression).Output);
            foreach (var optimize in new[] { false, true })
            {
                var (result, _) = Evaluator.RunCountedObserved(expr, enableOptimizations: optimize);
                AssertCountedValue(result, expectedValue, count);
            }

            var cache = new SuspendingAsyncZeroArgPropertyResultCache();
            var (asyncResult, _) = await AsyncEvaluationHarness.Complete(
                Evaluator.RunCountedObservedAsync(expr, zeroArgPropertyResultCache: cache));
            AssertCountedValue(asyncResult, expectedValue, count);
            Assert.Equal(0, cache.SyncAccesses);
        }
    }

    [Theory]
    [InlineData("()")]
    [InlineData("(1, 2)")]
    [InlineData("[]")]
    [InlineData("[1, 2]")]
    public async Task SelectionInLoopTemps_AndSubsequentStateReads_PreserveOneSlot(string selected)
    {
        foreach (var selection in new[] { "A:0", "first(A)", "A:(A.count - 1)", "last(A)" })
        {
            // Identical endpoints let every selector choose the same value. T is a
            // loop-local temporary; reading x in later iterations also exercises the
            // structured value after it has become state.
            var defs = "V = " + selected + "\nA = [V, V]\n";
            var step = "S(x, k) = { T = " + selection + "\nif(k == 0, T, x), k + 1";
            foreach (var (tail, call) in new[]
            {
                (" }\n", "repeat(S, 3, 0, 0)"),
                (", k < 3 }\n", "while(S, 0, 0)"),
            })
            {
                var (loops, _) = await AssertExecutionPaths(
                    defs + step + tail + call, "(" + selected + ", 3)", emittedCount: 2);
                Assert.True(loops.OptimizedLoopHits > 0);
                Assert.Contains(loops.LoopPlans, plan => plan.Optimized && plan.Temps.Any(temp => temp.Name == "T"));
                Assert.True(loops.PlannedExpressionHits > 0);
            }
        }
    }

    private static async Task<(LoopOptimizationDiagnosticsSnapshot Loops, SequencePipelineDiagnosticsSnapshot Sequences)>
        AssertExecutionPaths(string source, string expected, int emittedCount = 1)
    {
        var ast = new Expr.AlgorithmExpr(ParseValidRoot(source));
        var expectedValue = Success(expected).Value;
        var (generic, _) = Evaluator.RunCountedObserved(ast, enableOptimizations: false);
        AssertCountedValue(generic, expectedValue, emittedCount);

        var loops = new LoopOptimizationDiagnostics();
        var sequences = new SequencePipelineDiagnostics();
        var (planned, _) = Evaluator.RunCountedObserved(ast, loopDiagnostics: loops, sequenceDiagnostics: sequences);
        AssertCountedValue(planned, expectedValue, emittedCount);

        var cache = new SuspendingAsyncZeroArgPropertyResultCache();
        var (asyncResult, _) = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedObservedAsync(ast, zeroArgPropertyResultCache: cache));
        AssertCountedValue(asyncResult, expectedValue, emittedCount);
        Assert.Equal(0, cache.SyncAccesses);
        Assert.True(cache.AsyncAccesses > 0, "The async case must reach a suspending cache seam.");
        return (loops.GetSnapshot(), sequences.GetSnapshot());
    }

    private static void AssertCountedValue(EvalResult<Evaluator.CountedResult> result, Result expected, int count)
    {
        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : null);
        Assert.True(Result.ValueComparer.Equals(expected, result.Value.Value),
            $"Expected {SemanticExplorerHarness.Neutral(expected)}, got {AsyncEvaluationHarness.NeutralOf(result)}");
        Assert.Equal(count, result.Value.EmittedCount);
    }

    // ── Helpers ─────────────────────────────────────────────────────────────

    private static void AssertSameOutcome(RunResult expected, RunResult actual)
    {
        switch (expected)
        {
            case RunResult.Success expectedSuccess:
                var actualSuccess = Assert.IsType<RunResult.Success>(actual);
                Assert.True(
                    Result.ValueComparer.Equals(expectedSuccess.Value, actualSuccess.Value),
                    $"Expected {expectedSuccess.ToDisplayString()} but got {actualSuccess.ToDisplayString()}");
                Assert.Equal(expectedSuccess.EmittedCount, actualSuccess.EmittedCount);
                break;
            case RunResult.EvalFailure expectedFailure:
                var actualFailure = Assert.IsType<RunResult.EvalFailure>(actual);
                var expectedError = Assert.Single(expectedFailure.Errors);
                var actualError = Assert.Single(actualFailure.Errors);
                Assert.Equal(expectedError.Code, actualError.Code);
                Assert.Equal(expectedError.Message, actualError.Message);
                break;
            default:
                Assert.Fail($"Unexpected oracle outcome: {expected}");
                break;
        }
    }

    private static void AssertLoopModesAndAsyncTwinAgree(string source)
    {
        var ast = new Expr.AlgorithmExpr(ParseValidRoot(source));
        var (generic, _) = Evaluator.RunCountedObserved(ast, enableOptimizations: false);
        var (planned, _) = Evaluator.RunCountedObserved(ast, enableOptimizations: true);
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(generic), AsyncEvaluationHarness.NeutralOf(planned));

        var cache = new PassThroughAsyncZeroArgPropertyResultCache();
        var (asyncResult, _) = AsyncEvaluationHarness
            .Complete(Evaluator.RunCountedObservedAsync(ast, zeroArgPropertyResultCache: cache))
            .GetAwaiter()
            .GetResult();
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(generic), AsyncEvaluationHarness.NeutralOf(asyncResult));
        Assert.Equal(0, cache.SyncAccesses);
    }
}
