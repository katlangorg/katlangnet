using KatLang.Tests.AsyncEvaluation;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using static KatLang.Tests.EvaluatorTestSupport;

namespace KatLang.Tests;

/// <summary>
/// THE COLLECTOR SUPPLY-BOUNDARY LAW (September 2026).
///
/// <para>A collecting parameter consumes its allocated argument supply. Multiple
/// supplied items are collected exactly. If its entire segment is one lone
/// non-spread sequence value, that sequence may provide the collector's whole
/// supply, opening exactly one level. Lists remain exact. Items already produced
/// by explicit spread are final supplied items. The rule is applied to the segment
/// the ordinary binder allocated to the collector — AFTER fixed prefix/suffix
/// allocation — and it reads only slot provenance (a non-spread written slot versus
/// an explicit-spread-produced item), never result provenance: dot-call is ordinary
/// receiver injection, selection chooses a value, and no origin of a value changes
/// how the collector treats it.</para>
///
/// <para>Lean: <c>collectorSupply</c> applied inside <c>bindParameterPatternList</c>
/// and <c>bindCountedParameterPatternList</c>; <c>SupplyOrigin</c> recorded by
/// <c>collectVariadicCallItems</c>; laws <c>collector_*</c> in
/// <c>lean/KatLangArityLaws.lean</c>; CoreTests <c>CollectorSupplyBoundary</c>.
/// C#: <c>Evaluator.CollectorSupply</c>, <c>SupplyOrigin</c>.</para>
/// </summary>
public class CollectorSupplyBoundaryTests
{
    private const string Coll = "Coll(*xs) = xs\n";

    private static string Display(string source)
    {
        var provenance = SourceProvenance.ParseValid(source);
        var run = KatLangEngine.Run(source);
        Assert.True(run is RunResult.Success, source + "\n" + run.ToDisplayString());
        var success = Assert.IsType<RunResult.Success>(run);
        _ = provenance;
        return success.ToDisplayString().ReplaceLineEndings("\n");
    }

    // ── 1. The permanent regression matrix ──────────────────────────────────

    /// <summary>The required table, written as direct calls.</summary>
    public static TheoryData<string, string> DirectTable => new()
    {
        { "Coll()", "[]" },
        { "Coll(1)", "[1]" },
        { "Coll(1, 2)", "[1, 2]" },
        { "Coll(())", "[]" },
        { "Coll((1, 2))", "[1, 2]" },
        { "Coll(((), 3))", "[(), 3]" },
        { "Coll(((1, 2), 3))", "[(1, 2), 3]" },
        { "Coll((), 3)", "[(), 3]" },
        { "Coll((1, 2), 3)", "[(1, 2), 3]" },
        { "Coll([])", "[[]]" },
        { "Coll([1, 2])", "[[1, 2]]" },
        { "Coll((1, 2)*)", "[1, 2]" },
        { "Coll([(1, 2)]*)", "[(1, 2)]" },
        { "Coll([()]*)", "[()]" },
        { "Coll([]*)", "[]" },
        { "Coll((1, 2)*, 3)", "[1, 2, 3]" },
    };

    /// <summary>The same table in the dotted spelling (`R.Coll(rest)` is `Coll(R, rest)`).</summary>
    public static TheoryData<string, string> DottedTable => new()
    {
        { "1.Coll", "[1]" },
        { "1.Coll(2)", "[1, 2]" },
        { "().Coll", "[]" },
        { "(1, 2).Coll", "[1, 2]" },
        { "((), 3).Coll", "[(), 3]" },
        { "((1, 2), 3).Coll", "[(1, 2), 3]" },
        { "().Coll(3)", "[(), 3]" },
        { "(1, 2).Coll(3)", "[(1, 2), 3]" },
        { "[].Coll", "[[]]" },
        { "[1, 2].Coll", "[[1, 2]]" },
        { "(1, 2)*.Coll", "[1, 2]" },
        { "[(1, 2)]*.Coll", "[(1, 2)]" },
        { "[()]*.Coll", "[()]" },
        { "[]*.Coll", "[]" },
        { "(1, 2)*.Coll(3)", "[1, 2, 3]" },
    };

    [Theory]
    [MemberData(nameof(DirectTable))]
    public void RequiredTable_DirectCalls(string expression, string expected)
    {
        Assert.Equal(expected, Display(Coll + expression));
        AssertStrategiesAgree(Coll + expression);
    }

    [Theory]
    [MemberData(nameof(DottedTable))]
    public void RequiredTable_DottedCalls(string expression, string expected)
    {
        Assert.Equal(expected, Display(Coll + expression));
        AssertStrategiesAgree(Coll + expression);
    }

    // ── 2. Origin independence: only the value and the slot's provenance count ──

    /// <summary>Every receiver expression below evaluates to the sequence value `(1, 2)`.</summary>
    public static TheoryData<string> PairOrigins =>
    [
        "(1, 2)",
        "((1, 2))",
        "A",
        "Make()",
        "if(true, (1, 2), 0)",
        "B:0",
        "first(B)",
        "last(C)",
        "Obj.M",
        "map(B, Id):0",
        "(A*)",
        "{1, 2}",
    ];

    private const string OriginDefinitions =
        Coll +
        "A = 1, 2\n" +
        "Make = (1, 2)\n" +
        "B = ((1, 2), 3)\n" +
        "C = (3, (1, 2))\n" +
        "Obj = {\n    public M = (1, 2)\n}\n" +
        "Id(x) = x\n";

    [Theory]
    [MemberData(nameof(PairOrigins))]
    public void LoneWrittenSequence_OpensOneLevel_WhateverItsOrigin(string receiver)
    {
        Assert.Equal("[1, 2]", Display(OriginDefinitions + "Coll(" + receiver + ")"));
        Assert.Equal("[1, 2]", Display(OriginDefinitions + receiver + ".Coll"));
        Assert.Equal("[1, 2]", Display(OriginDefinitions + "Coll(" + receiver + "*)"));
        Assert.Equal("[1, 2]", Display(OriginDefinitions + receiver + "*.Coll"));
    }

    [Theory]
    [MemberData(nameof(PairOrigins))]
    public void SequenceBesideAnotherItem_IsCollectedExactly_WhateverItsOrigin(string receiver)
    {
        Assert.Equal("[(1, 2), 3]", Display(OriginDefinitions + "Coll(" + receiver + ", 3)"));
        Assert.Equal("[(1, 2), 3]", Display(OriginDefinitions + receiver + ".Coll(3)"));
        Assert.Equal("[1, 2, 3]", Display(OriginDefinitions + "Coll(" + receiver + "*, 3)"));
        Assert.Equal("[1, 2, 3]", Display(OriginDefinitions + receiver + "*.Coll(3)"));
    }

    // ── 3. Empty sequences, lists, and selection ────────────────────────────

    [Fact]
    public void EmptySequence_IsTheSameRule_NeverASpecialCase()
    {
        const string defs = Coll + "E = ()\nA = ((), 3)\nFz(x) = ()\n";
        foreach (var lone in new[] { "Coll(E)", "E.Coll", "Coll(())", "().Coll", "Coll(A:0)", "(A:0).Coll", "Coll(first(A))", "first(A).Coll", "Coll(Fz(1))", "Fz(1).Coll", "Coll(E*)", "E*.Coll" })
            Assert.Equal("[]", Display(defs + lone));

        foreach (var beside in new[] { "Coll(E, 3)", "E.Coll(3)", "Coll((), 3)", "().Coll(3)", "Coll(A:0, 3)", "(A:0).Coll(3)", "Coll(first(A), 3)", "first(A).Coll(3)" })
            Assert.Equal("[(), 3]", Display(defs + beside));

        // Selection itself never erases `()`.
        Assert.Equal("()", Display(defs + "A:0"));
        Assert.Equal("()", Display(defs + "first(A)"));
    }

    [Fact]
    public void Lists_StayExact_UntilExplicitlySpread()
    {
        const string defs = Coll + "L = [1, 2]\nEL = []\nA = ([1, 2], 3)\nB = ([], 3)\n";
        foreach (var lone in new[] { "Coll(L)", "L.Coll", "Coll([1, 2])", "[1, 2].Coll", "Coll(A:0)", "(A:0).Coll", "Coll(first(A))", "first(A).Coll" })
            Assert.Equal("[[1, 2]]", Display(defs + lone));
        foreach (var spread in new[] { "Coll(L*)", "L*.Coll", "Coll([1, 2]*)", "[1, 2]*.Coll", "Coll((A:0)*)", "(A:0)*.Coll" })
            Assert.Equal("[1, 2]", Display(defs + spread));

        foreach (var lone in new[] { "Coll(EL)", "EL.Coll", "Coll([])", "[].Coll", "Coll(B:0)", "(B:0).Coll" })
            Assert.Equal("[[]]", Display(defs + lone));
        foreach (var spread in new[] { "Coll(EL*)", "EL*.Coll", "Coll([]*)", "[]*.Coll", "Coll((B:0)*)", "(B:0)*.Coll" })
            Assert.Equal("[]", Display(defs + spread));

        Assert.Equal("[1, 2]", Display(defs + "A:0"));
        Assert.Equal("[1, 2]", Display(defs + "first(A)"));
    }

    [Fact]
    public void SelectionRemainsAValue_AndTheCollectorSeesOnlyThatValue()
    {
        const string defs = Coll + "A = ((1, 2), 3)\n";
        Assert.Equal("(1, 2)", Display(defs + "A:0"));
        Assert.Equal("(1, 2)", Display(defs + "first(A)"));
        Assert.Equal("(1, 2)", Display(defs + "X = A:0\nX"));
        foreach (var lone in new[] { "Coll(A:0)", "(A:0).Coll", "Coll(first(A))", "first(A).Coll", "Coll(last((3, A:0)))", "X = A:0\nColl(X)", "X = A:0\nX.Coll" })
            Assert.Equal("[1, 2]", Display(defs + lone));
        foreach (var beside in new[] { "Coll(A:0, 3)", "(A:0).Coll(3)", "Coll(first(A), 3)", "first(A).Coll(3)", "X = A:0\nColl(X, 3)", "X = A:0\nX.Coll(3)" })
            Assert.Equal("[(1, 2), 3]", Display(defs + beside));

        // first(A) ≡ A:0 and last(A) ≡ A:(A.count - 1) through the collector too.
        Assert.Equal(Display(defs + "Coll(A:0)"), Display(defs + "Coll(first(A))"));
        Assert.Equal(Display(defs + "Coll(A:(A.count - 1))"), Display(defs + "Coll(last(A))"));
    }

    // ── 4. Normalization and nesting ────────────────────────────────────────

    [Fact]
    public void RedundantGrouping_CreatesNoDistinction_AndOpeningIsOneLevel()
    {
        Assert.Equal(Display(Coll + "Coll((1, 2))"), Display(Coll + "Coll(((1, 2)))"));
        Assert.Equal(Display(Coll + "Coll(((), 3))"), Display(Coll + "Coll((((), 3)))"));
        Assert.Equal("[1, 2]", Display(Coll + "Coll(((1, 2)))"));
        Assert.Equal("[(), 3]", Display(Coll + "Coll((((), 3)))"));

        // One level only: sequence-valued items of the opened sequence stay values.
        Assert.Equal("[(1, 2), (3, 4)]", Display(Coll + "Coll(((1, 2), (3, 4)))"));
        Assert.Equal("[((1, 2), 3), 4]", Display(Coll + "Coll((((1, 2), 3), 4))"));
        Assert.Equal("[[1, 2], 3]", Display(Coll + "Coll(([1, 2], 3))"));
    }

    // ── 5. Fixed parameters and mixed signatures ────────────────────────────

    [Fact]
    public void FixedParameters_BindTheirValuesUnchanged()
    {
        const string defs = "Id(x) = x\nAdd(x, y) = x + y\n";
        Assert.Equal("(1, 2)", Display(defs + "Id((1, 2))"));
        Assert.Equal("(1, 2)", Display(defs + "(1, 2).Id"));
        Assert.Equal("3", Display(defs + "Add((1, 2)*)"));
        Assert.Equal("3", Display(defs + "(1, 2)*.Add"));

        var direct = SourceProvenance.ParseValid(defs + "Add((1, 2))").ExpectEvaluationError<EvalError.ArityMismatch>();
        Assert.Equal(2, direct.Expected);
        Assert.Equal(1, direct.Actual);
        var dotted = SourceProvenance.ParseValid(defs + "(1, 2).Add").ExpectEvaluationError<EvalError.ArityMismatch>();
        Assert.Equal(2, dotted.Expected);
        Assert.Equal(1, dotted.Actual);
    }

    [Theory]
    // *xs, z — the suffix allocates first; then the collector's segment decides.
    [InlineData("F(*xs, z) = xs, z", "F((1, 2), 3)", "([1, 2], 3)")]
    [InlineData("F(*xs, z) = xs, z", "F((1, 2), 3, 4)", "([(1, 2), 3], 4)")]
    [InlineData("F(*xs, z) = xs, z", "F([(1, 2)]*, 3)", "([(1, 2)], 3)")]
    [InlineData("F(*xs, z) = xs, z", "F((1, 2))", "([], (1, 2))")]
    [InlineData("F(*xs, z) = xs, z", "F((1, 2)*)", "([1], 2)")]
    [InlineData("F(*xs, z) = xs, z", "F((), 3)", "([], 3)")]
    [InlineData("F(*xs, z) = xs, z", "F([1, 2], 3)", "([[1, 2]], 3)")]
    // x, *rest — the prefix allocates first.
    [InlineData("F(x, *rest) = x, rest", "F(1, (2, 3))", "(1, [2, 3])")]
    [InlineData("F(x, *rest) = x, rest", "F(1, (2, 3), 4)", "(1, [(2, 3), 4])")]
    [InlineData("F(x, *rest) = x, rest", "F((1, 2))", "((1, 2), [])")]
    [InlineData("F(x, *rest) = x, rest", "F(1, ())", "(1, [])")]
    [InlineData("F(x, *rest) = x, rest", "F(1, [2, 3])", "(1, [[2, 3]])")]
    [InlineData("F(x, *rest) = x, rest", "F(1, [(2, 3)]*)", "(1, [(2, 3)])")]
    // x, *middle, z — both fixed ends allocate first.
    [InlineData("F(x, *middle, z) = x, middle, z", "F(0, (1, 2), 3)", "(0, [1, 2], 3)")]
    [InlineData("F(x, *middle, z) = x, middle, z", "F(0, (1, 2), 3, 4)", "(0, [(1, 2), 3], 4)")]
    [InlineData("F(x, *middle, z) = x, middle, z", "F(0, 3)", "(0, [], 3)")]
    [InlineData("F(x, *middle, z) = x, middle, z", "F(0, (), 3)", "(0, [], 3)")]
    [InlineData("F(x, *middle, z) = x, middle, z", "F(0, [1, 2], 3)", "(0, [[1, 2]], 3)")]
    [InlineData("F(x, *middle, z) = x, middle, z", "F((1, 2)*)", "(1, [], 2)")]
    public void MixedSignatures_ApplyTheRuleAfterFixedAllocation(string definition, string call, string expected)
    {
        Assert.Equal(expected, Display(definition + "\n" + call));
        AssertStrategiesAgree(definition + "\n" + call);

        // The dotted spelling of the same call: the first argument becomes the receiver.
        var open = call.IndexOf('(');
        var inner = call[(open + 1)..^1];
        if (inner.Length > 0)
        {
            var (receiver, rest) = SplitFirstArgument(inner);
            var callee = call[..open];
            var dotted = definition + "\n" + receiver + "." + callee + (rest is null ? "" : "(" + rest + ")");
            Assert.Equal(expected, Display(dotted));
        }
    }

    [Theory]
    [InlineData("F(*xs, z) = xs, z", "F()", 1, 0)]
    [InlineData("F(x, *rest) = x, rest", "F()", 1, 0)]
    [InlineData("F(x, *middle, z) = x, middle, z", "F()", 2, 0)]
    [InlineData("F(x, *middle, z) = x, middle, z", "F((1, 2))", 2, 1)]
    [InlineData("F(x, *middle, z) = x, middle, z", "F(())", 2, 1)]
    [InlineData("F(x, *middle, z) = x, middle, z", "F([1, 2])", 2, 1)]
    [InlineData("F(x, *middle, z) = x, middle, z", "F([1, 2, 3, 4])", 2, 1)]
    public void Arity_CountsSuppliedItems_NeverASequenceElementCount(string definition, string call, int expectedMinimum, int actual)
    {
        var error = SourceProvenance.ParseValid(definition + "\n" + call)
            .ExpectEvaluationError<EvalError.VariadicArityMismatch>();
        Assert.Equal(expectedMinimum, error.ExpectedMinimum);
        Assert.Equal(actual, error.Actual);
    }

    // ── 6. Provenance is slot provenance, never result provenance ───────────

    [Fact]
    public void WrittenSlot_AndExplicitSpreadItem_HoldingTheSameValue_AreDistinguished()
    {
        Assert.Equal("[1, 2]", Display(Coll + "Coll((1, 2))"));
        Assert.Equal("[(1, 2)]", Display(Coll + "Coll([(1, 2)]*)"));
        Assert.Equal("[()]", Display(Coll + "Coll([()]*)"));
        Assert.Equal("[]", Display(Coll + "Coll(())"));
        Assert.Equal("[(1, 2), 3]", Display(Coll + "Coll([(1, 2)]*, 3)"));
        Assert.Equal("[1, 2]", Display(Coll + "Coll([(1, 2)]**)"));

        // A captured spread is a written slot again (`(A*)` is one value), whatever
        // the spread produced: the capture of `[(1, 2)]*` is the value `(1, 2)`.
        Assert.Equal("[1, 2]", Display(Coll + "Coll(([(1, 2)]*))"));
        Assert.Equal("[1, 2]", Display(Coll + "([(1, 2)]*).Coll"));
    }

    [Theory]
    [InlineData("(1, 2)", "[1, 2]", "[(1, 2)]")]
    [InlineData("()", "[]", "[()]")]
    [InlineData("[]", "[[]]", "[[]]")]
    [InlineData("[1, 2]", "[[1, 2]]", "[[1, 2]]")]
    [InlineData("((1, 2), 3)", "[(1, 2), 3]", "[((1, 2), 3)]")]
    public void SpreadOrigin_EndsAtValueBoundaries(string value, string written, string final)
    {
        var definitions = Coll + "V = " + value + "\nId(x) = x\n" +
            "Stored = Id([V]*)\nTarget(*xs) = xs\nUse(xs) = Target\n";
        Assert.Equal(final, Display(definitions + "Coll([V]*)"));
        foreach (var expression in new[]
        {
            "V", "Id([V]*)", "Stored", "if(true, Id([V]*), 0)",
            "Coll([V]*):0", "first(Coll([V]*))", "last(Coll([V]*))",
            "[Id([V]*)]:0", "map([V], Id):0", "(Coll([V]*)*)",
        })
        {
            // map requires one emitted callback value; Id(()) emits zero.
            if (value == "()" && expression == "map([V], Id):0") continue;
            Assert.Equal(written, Display(definitions + "Coll(" + expression + ")"));
            Assert.Equal(written, Display(definitions + "(" + expression + ").Coll"));
            Assert.Equal("[" + value + ", 9]", Display(definitions + "Coll(" + expression + ", 9)"));
        }

        // Fixed binding and implicit forwarding create a fresh written slot;
        // repeated property reads exercise the cached value too.
        Assert.Equal(written, Display(definitions + "Use([V]*)"));
        Assert.Equal(written + "\n" + written, Display(definitions + "Coll(Stored), Coll(Stored)"));
        AssertStrategiesAgree(definitions + "Coll(Stored), Use([V]*), Coll(Stored, 9)");
    }

    [Theory]
    [InlineData("F([]*, (1, 2), []*, 3)", "([1, 2], 3)")]
    [InlineData("F([]*, [(1, 2)]*, []*, 3)", "([(1, 2)], 3)")]
    [InlineData("F([()]*, []*, 3)", "([()], 3)")]
    [InlineData("F([]*, (), []*, 3)", "([], 3)")]
    public void EmptySpreadSlots_DoNotChangeTheOriginOfRemainingItems(string call, string expected)
        => Assert.Equal(expected, Display("F(*xs, z) = xs, z\n" + call));

    [Theory]
    [InlineData("(1, 2)", "[1, 2]")]
    [InlineData("()", "[]")]
    [InlineData("[]", "[[]]")]
    [InlineData("[1, 2]", "[[1, 2]]")]
    [InlineData("((1, 2), 3)", "[(1, 2), 3]")]
    public void ReducerElementSideCollector_ReceivesOneWrittenItem(string item, string expected)
    {
        var source = "R(*items, acc) = items\nreduce([" + item + "], R, 99)";
        Assert.Equal(expected, Display(source));
        AssertStrategiesAgree(source);
    }

    // ── 7. Nested patterns, callbacks, loops, deconstruction, builtins ──────

    [Fact]
    public void NestedPatterns_KeepOneLevelOpening_AndNeverReopenPatternItems()
    {
        const string defs = "Pat((x, *y)) = [x], y\nPat2((x, *y), z) = [x], y, [z]\n";
        Assert.Equal("([1], [2, 3])", Display(defs + "Pat((1, 2, 3))"));
        Assert.Equal("([1], [(2, 3)])", Display(defs + "Pat((1, (2, 3)))"));
        Assert.Equal("([1], [[2, 3]])", Display(defs + "Pat((1, [2, 3]))"));
        Assert.Equal("([1], [(2, 3)], [9])", Display(defs + "Pat2((1, (2, 3)), 9)"));
        Assert.Equal("([1], [(2, 3)], [9])", Display(defs + "(1, (2, 3)).Pat2(9)"));
    }

    [Fact]
    public void Callbacks_UseTheSameLaw_ThroughTheOrdinaryCallbackBinder()
    {
        const string defs = Coll + "Rest(a, *rest) = rest\n";
        // A whole callback item is the collector's lone written slot.
        Assert.Equal("[[1, 2], [3, 4]]", Display(defs + "((1, 2), (3, 4)).map(Coll)"));
        Assert.Equal("[[], [3, 4]]", Display(defs + "((), (3, 4)).map(Coll)"));
        Assert.Equal("[[[1, 2]], [[3]]]", Display(defs + "([1, 2], [3]).map(Coll)"));
        Assert.Equal("[[7], [8]]", Display(defs + "(7, 8).map(Coll)"));
        Assert.Equal("[[(1, 2), 3]]", Display(defs + "[((1, 2), 3)].map(Coll)"));
        // The flat-callback row convention opens a lone sequence item into row slots for a
        // multi-parameter callee; those row slots are FINAL, so a nested pair is not reopened.
        Assert.Equal("[[(2, 3)], [5]]", Display(defs + "((1, (2, 3)), (4, 5)).map(Rest)"));
        Assert.Equal("[[2, 3]]", Display(defs + "[(1, 2, 3)].map(Rest)"));
        // A reducer with a collecting accumulator side binds the accumulator's own
        // one-level slots (`Result.ToItems`), which are final: a sequence-valued slot
        // stays one item and a list accumulator stays one opaque slot.
        Assert.Equal("[(1, 2), 3]", Display("Acc(x, *acc) = acc\nreduce([9], Acc, ((1, 2), 3))"));
        Assert.Equal("[1, 2]", Display("Acc(x, *acc) = acc\nreduce([9], Acc, (1, 2))"));
        Assert.Equal("[]", Display("Acc(x, *acc) = acc\nreduce([9], Acc, ())"));
        Assert.Equal("[[1, 2]]", Display("Acc(x, *acc) = acc\nreduce([9], Acc, [1, 2])"));
        Assert.Equal("[[(1, 2)]]", Display("Acc(x, *acc) = acc\nreduce([9], Acc, [(1, 2)])"));
        AssertStrategiesAgree(defs + "((1, 2), (3, 4)).map(Coll)");
        AssertStrategiesAgree(defs + "((1, (2, 3)), (4, 5)).map(Rest)");
    }

    [Fact]
    public void FilterCountFusion_BindsCollectingPredicates_LikeTheGenericPath()
    {
        const string source = "P(*xs) = xs.count == 2\n((1, 2), 3, (4, 5), [6, 7]).filter(P).count";
        var sequence = new SequencePipelineDiagnostics();
        var (fused, _) = Evaluator.RunCountedObserved(AsyncEvaluationHarness.Ast(source), sequenceDiagnostics: sequence);
        var (generic, _) = Evaluator.RunCountedObserved(AsyncEvaluationHarness.Ast(source), enableOptimizations: false);
        Assert.True(fused.IsOk, fused.IsError ? fused.Error.ToString() : "");
        // (1, 2) and (4, 5) open to two items each; 3 is one item; [6, 7] is one exact item.
        Assert.Equal("2", Assert.IsType<Result.Atom>(fused.Value.Value).Value.ToString());
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(generic), AsyncEvaluationHarness.NeutralOf(fused));
        Assert.Equal(1, sequence.GetSnapshot().FilterCountFusionHits);
    }

    [Fact]
    public void LoopStateSlots_AreFinalItems_AndCollectingStepsDeclinePlanning()
    {
        // A loop step is never called with written arguments: its state slots are an
        // established supply, so a collecting step collects them exactly — a lone
        // sequence-valued state slot is NOT opened.
        const string source = "Step(*xs) = xs.count\nrepeat(Step, 1, (1, 2)), repeat(Step, 1, 1, 2), repeat(Step, 1, [1, 2])";
        Assert.Equal("1\n2\n1", Display(source));
        var ast = AsyncEvaluationHarness.Ast(source);
        var loop = new LoopOptimizationDiagnostics();
        var (planned, _) = Evaluator.RunCountedObserved(ast, loopDiagnostics: loop);
        var (generic, _) = Evaluator.RunCountedObserved(ast, enableOptimizations: false);
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(generic), AsyncEvaluationHarness.NeutralOf(planned));

        Assert.Equal(0, loop.OptimizedLoopHits);
        Assert.Equal(3, loop.FallbackReasons["variadic loop step"]);

        // The same law for the mixed step shape, whose suffix consumes the last slot.
        const string mixed = "Step(*xs, last) = xs.count, last\nrepeat(Step, 1, (1, 2), 3), repeat(Step, 1, (1, 2), 3, 4)";
        Assert.Equal("(1, 3)\n(2, 4)", Display(mixed));
    }

    [Theory]
    [InlineData("(1, 2)", "[1, 2]\n2")]
    [InlineData("()", "[]\n2")]
    [InlineData("[1, 2]", "[[1, 2]]\n2")]
    public void CollectorInLoopTemp_ReentersThroughAWrittenSlot(string value, string expected)
    {
        var source = Coll + "V = " + value + "\n" +
            "S(x, k) = { T = Coll(if(k == 0, V, x))\nif(k == 0, T, x), k + 1 }\n" +
            "repeat(S, 2, 0, 0)";
        Assert.Equal(expected, Display(source));
        var ast = AsyncEvaluationHarness.Ast(source);
        var loop = new LoopOptimizationDiagnostics();
        var (planned, _) = Evaluator.RunCountedObserved(ast, loopDiagnostics: loop);
        var (generic, _) = Evaluator.RunCountedObserved(ast, enableOptimizations: false);
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(generic), AsyncEvaluationHarness.NeutralOf(planned));
        Assert.Equal(2, planned.Value.EmittedCount);
        var snapshot = loop.GetSnapshot();
        Assert.True(snapshot.OptimizedLoopHits > 0);
        Assert.True(snapshot.PlannedExpressionHits > 0);
        Assert.Contains(snapshot.LoopPlans, plan => plan.Optimized && plan.Temps.Any(temp => temp.Name == "T"));
    }

    [Fact]
    public void Deconstruction_KeepsItsOwnOneLevelOpeningRule()
    {
        // Deconstruction is the UNPACKING receiver: it opens one lone sequence or list
        // boundary of its shared right-hand side, and its collecting target collects the
        // matched items exactly — those items are pattern-opened, hence final, so a
        // sequence-valued item is never reopened by the collector rule.
        Assert.Equal("(1, [2, 3], 4)", Display("x, *y, z = (1, 2, 3, 4)\n(x, y, z)"));
        Assert.Equal("(1, [(2, 3)], 4)", Display("x, *y, z = (1, (2, 3), 4)\n(x, y, z)"));
        Assert.Equal("(1, [[2, 3]], 4)", Display("x, *y, z = (1, [2, 3], 4)\n(x, y, z)"));
        Assert.Equal("(1, [2, 3])", Display("first, *rest = [1, 2, 3]\n(first, rest)"));
        Assert.Equal("(1, [])", Display("first, *rest = 1\n(first, rest)"));
        Assert.Equal("[1, (2, 3)]", Display("*all = (1, (2, 3))\nall"));
    }

    [Fact]
    public void CollectionBuiltins_KeepTheirFixedCollectionParameter()
    {
        const string defs = "A = (1, 2)\nL = [1, 2]\nN = ((1, 2), 3)\n";
        Assert.Equal("2\n2\n2\n2", Display(defs + "count(A), A.count, count(L), L.count"));
        Assert.Equal("3\n3", Display(defs + "sum(A), A.sum"));
        Assert.Equal("2\n2", Display(defs + "count(N), N.count"));
        Assert.Equal("0\n0\n0", Display(defs + "count(()), ().count, count([])"));
        var direct = SourceProvenance.ParseValid(defs + "count(A*)").ExpectEvaluationError<EvalError.ArityMismatch>();
        Assert.Equal(1, direct.Expected);
        Assert.Equal(2, direct.Actual);
    }

    // ── 8. Async: a genuinely suspended run follows the same binding law ────

    [Theory]
    [InlineData("Coll(Pair())", "[1, 2]")]
    [InlineData("Pair().Coll", "[1, 2]")]
    [InlineData("Coll(Pair(), 3)", "[(1, 2), 3]")]
    [InlineData("Pair().Coll(3)", "[(1, 2), 3]")]
    [InlineData("Coll(Pair()*)", "[1, 2]")]
    [InlineData("F(Pair(), 3)", "([1, 2], 3)")]
    [InlineData("F(Pair(), 3, 4)", "([(1, 2), 3], 4)")]
    [InlineData("G(1, Pair())", "(1, [1, 2])")]
    [InlineData("G(1, Pair(), 3)", "(1, [(1, 2), 3])")]
    [InlineData("Coll(Empty())", "[]")]
    [InlineData("Coll(Empty(), 3)", "[(), 3]")]
    [InlineData("Coll(Items())", "[[1, 2]]")]
    public async Task SuspendedAsyncRun_BindsExactlyLikeTheSynchronousRun(string expression, string expected)
    {
        const string definitions = Coll + "F(*xs, z) = xs, z\nG(x, *rest) = x, rest\n";
        var source = definitions + expression;
        var pair = new Result.SequenceValue([new Result.Atom(1), new Result.Atom(2)]);
        var empty = new Result.SequenceValue([]);
        var items = new Result.ListValue([new Result.Atom(1), new Result.Atom(2)]);

        // The synchronous oracle: host operations that return immediately.
        var syncOperations = HostOperations.Create(
            HostOperation.Create("Pair", (_, _) => pair),
            HostOperation.Create("Empty", (_, _) => empty),
            HostOperation.Create("Items", (_, _) => items));
        var syncOptions = new RunOptions { HostOperations = syncOperations };
        var syncRun = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source, syncOptions));
        Assert.Equal(expected, syncRun.ToDisplayString().ReplaceLineEndings("\n"));
        var syncResult = Evaluator.RunCountedObserved(
            new Expr.AlgorithmExpr((await SourceProvenance.ParseValidAsync(source, syncOptions)).Root),
            enableOptimizations: false,
            hostOperations: syncOperations).Result;
        Assert.True(syncResult.IsOk);

        // The genuinely suspended run: every host operation parks until released,
        // and the run is observably incomplete while it is held.
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        HostOperation Suspending(string name, Result value) => HostOperation.CreateAsync(name, async (_, _) =>
        {
            entered.TrySetResult();
            await release.Task;
            return value;
        });
        var asyncOperations = HostOperations.Create(Suspending("Pair", pair), Suspending("Empty", empty), Suspending("Items", items));
        var asyncOptions = new RunOptions { HostOperations = asyncOperations };
        var parsed = await SourceProvenance.ParseValidAsync(source, asyncOptions);
        var pending = Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(parsed.Root), hostOperations: asyncOperations).AsTask();
        await entered.Task.WaitAsync(TimeSpan.FromSeconds(10));
        Assert.False(pending.IsCompleted);
        release.SetResult();
        var asyncResult = (await pending.WaitAsync(TimeSpan.FromSeconds(10))).Result;

        Assert.True(asyncResult.IsOk, asyncResult.IsError ? asyncResult.Error.ToString() : "");
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(syncResult), AsyncEvaluationHarness.NeutralOf(asyncResult));
        Assert.True(Result.ValueComparer.Equals(syncResult.Value.Value, asyncResult.Value.Value));
        Assert.Equal(syncResult.Value.EmittedCount, asyncResult.Value.EmittedCount);
    }

    [Theory]
    [InlineData(false, false, false)]
    [InlineData(true, false, false)]
    [InlineData(false, true, false)]
    [InlineData(true, true, false)]
    [InlineData(false, false, true)]
    [InlineData(true, true, true)]
    public async Task SuspendedSlots_AreEvaluatedOnceInOrder_BeforeBinding(bool dotted, bool spread, bool fail)
    {
        var middle = spread ? "Middle()*" : "first(Middle())";
        var tail = fail ? "Right() / 0" : "Right()";
        var call = dotted ? "Left().F(" + middle + ", " + tail + ")"
            : "F(Left(), " + middle + ", " + tail + ")";
        var source = "F(x, *xs, z) = xs\n" + call;
        string[] names = ["Left", "Middle", "Right"];
        Result[] values = [new Result.Atom(0),
            new Result.ListValue([new Result.SequenceValue([new Result.Atom(1), new Result.Atom(2)])]),
            new Result.Atom(3)];
        var syncOperations = HostOperations.Create(names.Select((name, index) =>
            HostOperation.Create(name, (_, _) => values[index])).ToArray());
        var syncOptions = new RunOptions { HostOperations = syncOperations };
        var syncRoot = (await SourceProvenance.ParseValidAsync(source, syncOptions)).Root;
        var (sync, syncBudget) = Evaluator.RunCountedObserved(new Expr.AlgorithmExpr(syncRoot),
            enableOptimizations: false, hostOperations: syncOperations);
        if (fail)
            Assert.Equal(KatLangErrorCode.DivisionByZero, sync.Error.Code);
        else
        {
            var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source, syncOptions));
            Assert.Equal(spread ? "[(1, 2)]" : "[1, 2]", success.ToDisplayString());
            Assert.Equal(1, sync.Value.EmittedCount);
        }

        var entered = names.Select(_ => new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously)).ToArray();
        var release = names.Select(_ => new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously)).ToArray();
        var calls = new int[names.Length];
        var operations = HostOperations.Create(names.Select((name, index) =>
            HostOperation.CreateAsync(name, async (_, _) =>
            {
                Interlocked.Increment(ref calls[index]);
                entered[index].TrySetResult();
                await release[index].Task;
                return values[index];
            })).ToArray());
        var root = (await SourceProvenance.ParseValidAsync(source, new RunOptions { HostOperations = operations })).Root;
        var pending = Evaluator.RunCountedObservedAsync(new Expr.AlgorithmExpr(root), hostOperations: operations).AsTask();
        try
        {
            for (var index = 0; index < names.Length; index++)
            {
                await entered[index].Task.WaitAsync(TimeSpan.FromSeconds(10));
                Assert.False(pending.IsCompleted);
                Assert.Equal(Enumerable.Range(0, names.Length).Select(i => i <= index ? 1 : 0), calls);
                release[index].SetResult();
            }
            var (actual, budget) = await pending.WaitAsync(TimeSpan.FromSeconds(10));
            Assert.Equal(AsyncEvaluationHarness.NeutralOf(sync), AsyncEvaluationHarness.NeutralOf(actual));
            Assert.Equal(syncBudget.ConsumedSteps, budget.ConsumedSteps);
            Assert.Equal(new[] { 1, 1, 1 }, calls);
        }
        finally
        {
            foreach (var gate in release) gate.TrySetResult();
        }
    }

    // ── Helpers ─────────────────────────────────────────────────────────────

    private static (string Receiver, string? Remainder) SplitFirstArgument(string arguments)
    {
        var depth = 0;
        for (var index = 0; index < arguments.Length; index++)
        {
            var c = arguments[index];
            if (c is '(' or '[') depth++;
            else if (c is ')' or ']') depth--;
            else if (c == ',' && depth == 0)
                return (arguments[..index], arguments[(index + 1)..].TrimStart());
        }

        return (arguments, null);
    }

    private static void AssertStrategiesAgree(string source)
    {
        var ast = new Expr.AlgorithmExpr(ParseValidRoot(source));
        var (generic, genericBudget) = Evaluator.RunCountedObserved(ast, enableOptimizations: false);
        var (planned, _) = Evaluator.RunCountedObserved(ast, enableOptimizations: true);
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(generic), AsyncEvaluationHarness.NeutralOf(planned));

        var cache = new PassThroughAsyncZeroArgPropertyResultCache();
        var (asyncResult, asyncBudget) = AsyncEvaluationHarness
            .Complete(Evaluator.RunCountedObservedAsync(ast, zeroArgPropertyResultCache: cache))
            .GetAwaiter()
            .GetResult();
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(generic), AsyncEvaluationHarness.NeutralOf(asyncResult));
        Assert.Equal(genericBudget.ConsumedSteps, asyncBudget.ConsumedSteps);
        Assert.Equal(0, cache.SyncAccesses);
    }
}
