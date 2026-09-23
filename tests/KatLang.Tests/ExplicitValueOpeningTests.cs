using KatLang.Tests.AsyncEvaluation;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;
using static KatLang.Tests.EvaluatorTestSupport;

namespace KatLang.Tests;

/// <summary>
/// VALUES STAY VALUES: EXPLICIT VALUE OPENING (September 2026).
///
/// <para>A non-spread argument supplies exactly ONE item — its value, whatever that
/// value is (a scalar, a sequence, a list, <c>()</c>, <c>[]</c>). Only an explicit
/// spread <c>v*</c> turns one value into several supplied items (one level, a sequence
/// and a list alike), and only an explicit structural pattern (<c>F((x, y))</c>,
/// <c>x, *r = v</c>) opens a received value. Fixed parameters bind their allocated item
/// unchanged; a collecting parameter collects exactly its allocated items as one list
/// (THE EXACT COLLECTOR LAW); a callback receives each element — and a reducer its
/// accumulator — as ONE ordinary argument (THE CALLBACK LAW). No collector, callback,
/// reducer, dot-call, selection, alias, or forwarding mechanism opens a value on the
/// programmer's behalf.</para>
///
/// <para>Lean: <c>collectVariadicCallItems</c> (one item per non-spread slot),
/// <c>collectSegment</c> in <c>bindParameterPatternList</c> /
/// <c>bindCountedParameterPatternList</c>, <c>evalUserCallbackCallCounted</c>; laws
/// <c>collector_*</c> / <c>explicit_spread_opens_one_level</c> /
/// <c>forwarding_resupplies_the_collected_items</c> in <c>lean/KatLangArityLaws.lean</c>;
/// algebra <c>bindArgs</c> / <c>bindCallback</c>; CoreTests <c>ExplicitValueOpening</c>.
/// C#: <c>Evaluator.BuildCallArgumentInputs</c>, <c>CollectSegment</c>,
/// <c>EvalResolvedCallbackCallCountedCore</c>.</para>
/// </summary>
public class ExplicitValueOpeningTests
{
    private const string Coll = "Coll(*xs) = xs\n";

    private static string Display(string source)
    {
        _ = SourceProvenance.ParseValid(source);
        var run = KatLangEngine.Run(source);
        Assert.True(run is RunResult.Success, source + "\n" + run.ToDisplayString());
        return Assert.IsType<RunResult.Success>(run).ToDisplayString().ReplaceLineEndings("\n");
    }

    /// <summary>
    /// A comparable outcome: the display of a successful run, or the error CODE of a
    /// failed one (the direct call and a callback may report different arity payloads —
    /// a fixed-arity or a variadic mismatch — for the same one-argument supply, but they
    /// always classify alike).
    /// </summary>
    private static string Outcome(string source)
    {
        _ = SourceProvenance.ParseValid(source);
        return KatLangEngine.Run(source) switch
        {
            RunResult.Success success => "ok " + success.ToDisplayString().ReplaceLineEndings("\n"),
            RunResult.EvalFailure failure => "err " + failure.Errors[0].Code,
            var other => throw new InvalidOperationException(source + "\n" + other.ToDisplayString()),
        };
    }

    private static KatLangErrorCode FailureCode(string source)
    {
        _ = SourceProvenance.ParseValid(source);
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
        return failure.Errors[0].Code;
    }

    // ── 1. The required collector table ─────────────────────────────────────

    /// <summary>The required table, written as direct calls.</summary>
    public static TheoryData<string, string> DirectTable => new()
    {
        { "Coll()", "[]" },
        { "Coll(1)", "[1]" },
        { "Coll(1, 2)", "[1, 2]" },
        { "Coll(())", "[()]" },
        { "Coll((1, 2))", "[(1, 2)]" },
        { "Coll(((1, 2), 3))", "[((1, 2), 3)]" },
        { "Coll(((), 3))", "[((), 3)]" },
        { "Coll((), 3)", "[(), 3]" },
        { "Coll((1, 2), 3)", "[(1, 2), 3]" },
        { "Coll([])", "[[]]" },
        { "Coll([1, 2])", "[[1, 2]]" },
        { "Coll([[1, 2], 3])", "[[[1, 2], 3]]" },
        { "Coll((1, 2)*)", "[1, 2]" },
        { "Coll([1, 2]*)", "[1, 2]" },
        { "Coll([]*)", "[]" },
        { "Coll(()*)", "[]" },
        { "Coll([(1, 2)]*)", "[(1, 2)]" },
        { "Coll([()]*)", "[()]" },
        { "Coll([[1, 2]]*)", "[[1, 2]]" },
        { "Coll((1, 2)*, 3)", "[1, 2, 3]" },
    };

    /// <summary>The same table in the dotted spelling (`R.Coll(rest)` is `Coll(R, rest)`).</summary>
    public static TheoryData<string, string> DottedTable => new()
    {
        { "1.Coll", "[1]" },
        { "1.Coll(2)", "[1, 2]" },
        { "().Coll", "[()]" },
        { "(1, 2).Coll", "[(1, 2)]" },
        { "((), 3).Coll", "[((), 3)]" },
        { "((1, 2), 3).Coll", "[((1, 2), 3)]" },
        { "().Coll(3)", "[(), 3]" },
        { "(1, 2).Coll(3)", "[(1, 2), 3]" },
        { "[].Coll", "[[]]" },
        { "[1, 2].Coll", "[[1, 2]]" },
        { "(1, 2)*.Coll", "[1, 2]" },
        { "[1, 2]*.Coll", "[1, 2]" },
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

    [Fact]
    public void EmptyValues_AreOneItem_WhileOnlyTheirSpreadSuppliesNothing()
    {
        // Zero supplied items and one supplied item whose value is empty stay distinct.
        const string defs = Coll + "E = ()\nEL = []\nA = ((), 3)\nFz(x) = ()\n";
        foreach (var one in new[] { "Coll(E)", "E.Coll", "Coll(())", "().Coll", "Coll(A:0)", "(A:0).Coll",
                     "Coll(first(A))", "first(A).Coll", "Coll(Fz(1))", "Fz(1).Coll", "Coll(if(true, (), 1))" })
            Assert.Equal("[()]", Display(defs + one));
        foreach (var one in new[] { "Coll(EL)", "EL.Coll", "Coll([])", "[].Coll" })
            Assert.Equal("[[]]", Display(defs + one));
        foreach (var none in new[] { "Coll()", "Coll(E*)", "E*.Coll", "Coll(()*)", "Coll(EL*)", "EL*.Coll", "Coll([]*)" })
            Assert.Equal("[]", Display(defs + none));
        foreach (var beside in new[] { "Coll(E, 3)", "E.Coll(3)", "Coll((), 3)", "().Coll(3)", "Coll(A:0, 3)", "first(A).Coll(3)" })
            Assert.Equal("[(), 3]", Display(defs + beside));

        // Selection itself never erases `()`.
        Assert.Equal("()", Display(defs + "A:0"));
        Assert.Equal("()", Display(defs + "first(A)"));

        // The zero-argument value demand is untouched: a bare collector reference is `Coll()`.
        Assert.Equal("[]", Display(Coll + "Coll"));
        Assert.Equal("[]", Display(Coll + "X = Coll\nX"));
    }

    // ── 2. Counting arguments versus counting contents ──────────────────────

    [Fact]
    public void Collectors_CountSuppliedArguments_WhileCollectionValuesCountTheirContents()
    {
        const string defs = "Cnt(*xs) = xs.count\nCntValue(x) = x.count\n";
        Assert.Equal("0", Display(defs + "Cnt()"));
        Assert.Equal("1", Display(defs + "Cnt(7)"));
        Assert.Equal("1", Display(defs + "Cnt((10, 7))"));
        Assert.Equal("1", Display(defs + "Cnt([10, 7])"));
        Assert.Equal("2", Display(defs + "Cnt((10, 7)*)"));
        Assert.Equal("2", Display(defs + "Cnt([10, 7]*)"));
        Assert.Equal("2", Display(defs + "CntValue((10, 7))"));
        Assert.Equal("2", Display(defs + "CntValue([10, 7])"));
        Assert.Equal("2", Display(defs + "(10, 7).count"));
        Assert.Equal("2", Display(defs + "[10, 7].count"));
        AssertStrategiesAgree(defs + "Cnt((10, 7)), Cnt([10, 7]), Cnt((10, 7)*), CntValue([10, 7])");
    }

    [Fact]
    public void VariadicAlgorithms_AreArgumentVariadic()
    {
        const string defs = "Mean(*values) = values.sum / values.count\nValues = range(1, 3)\n";
        Assert.Equal("2", Display(defs + "Mean(1, 2, 3)"));
        Assert.Equal("2", Display(defs + "Mean((1, 2, 3)*)"));
        Assert.Equal("2", Display(defs + "Mean([1, 2, 3]*)"));
        Assert.Equal("2", Display(defs + "Values*.Mean"));

        // One sequence or list argument is ONE collected element: the numeric `sum`
        // rejects the structured element (Lean: the element-constraint `badArity`).
        foreach (var one in new[] { "Mean((1, 2, 3))", "Mean([1, 2, 3])", "Values.Mean", "(1, 2, 3).Mean" })
            Assert.Equal(KatLangErrorCode.ArityMismatch, FailureCode(defs + one));
    }

    // ── 3. Origin independence ─────────────────────────────────────────────

    /// <summary>Every expression below evaluates to the sequence value `(1, 2)`.</summary>
    public static TheoryData<string> PairOrigins =>
    [
        "(1, 2)",
        "((1, 2))",
        "A",
        "Make()",
        "Id((1, 2))",
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
    public void EveryOriginOfAValue_IsOneArgument_AndOnlyItsSpreadOpensIt(string receiver)
    {
        Assert.Equal("[(1, 2)]", Display(OriginDefinitions + "Coll(" + receiver + ")"));
        Assert.Equal("[(1, 2)]", Display(OriginDefinitions + receiver + ".Coll"));
        Assert.Equal("[1, 2]", Display(OriginDefinitions + "Coll(" + receiver + "*)"));
        Assert.Equal("[1, 2]", Display(OriginDefinitions + receiver + "*.Coll"));
        Assert.Equal("[(1, 2), 3]", Display(OriginDefinitions + "Coll(" + receiver + ", 3)"));
        Assert.Equal("[(1, 2), 3]", Display(OriginDefinitions + receiver + ".Coll(3)"));
        Assert.Equal("[1, 2, 3]", Display(OriginDefinitions + "Coll(" + receiver + "*, 3)"));
        Assert.Equal("(1, 2)", Display(OriginDefinitions + "Id(" + receiver + ")"));
    }

    [Fact]
    public void SequencesAndLists_AreTreatedAlike_AtEveryCallPosition()
    {
        const string defs = Coll + "S = (1, 2)\nL = [1, 2]\nG(x, *rest) = x, rest\nF(*xs, z) = xs, z\n";
        Assert.Equal("[(1, 2)]", Display(defs + "Coll(S)"));
        Assert.Equal("[[1, 2]]", Display(defs + "Coll(L)"));
        Assert.Equal(Display(defs + "Coll(S*)"), Display(defs + "Coll(L*)"));
        Assert.Equal("(0, [(1, 2)])", Display(defs + "G(0, S)"));
        Assert.Equal("(0, [[1, 2]])", Display(defs + "G(0, L)"));
        Assert.Equal("([(1, 2)], 9)", Display(defs + "F(S, 9)"));
        Assert.Equal("([[1, 2]], 9)", Display(defs + "F(L, 9)"));
    }

    // ── 4. Explicit spread: one level, never reopened ───────────────────────

    [Fact]
    public void SpreadItems_AreEstablishedItems_NeverReopened()
    {
        Assert.Equal("[(1, 2)]", Display(Coll + "Coll((1, 2))"));
        Assert.Equal("[(1, 2)]", Display(Coll + "Coll([(1, 2)]*)"));
        Assert.Equal("[()]", Display(Coll + "Coll([()]*)"));
        Assert.Equal("[[1, 2]]", Display(Coll + "Coll([[1, 2]]*)"));
        Assert.Equal("[(1, 2), 3]", Display(Coll + "Coll([(1, 2)]*, 3)"));
        Assert.Equal("[1, 2]", Display(Coll + "Coll([(1, 2)]**)"));

        // A captured spread is ONE value (`(A*)`): the capture of `[(1, 2)]*` is the
        // value `(1, 2)`, one argument; only a second spread opens it.
        Assert.Equal("[(1, 2)]", Display(Coll + "Coll(([(1, 2)]*))"));
        Assert.Equal("[(1, 2)]", Display(Coll + "([(1, 2)]*).Coll"));
        Assert.Equal("[1, 2]", Display(Coll + "Coll(([(1, 2)]*)*)"));
    }

    [Fact]
    public void RedundantGrouping_CreatesNoDistinction_AndOpeningIsOneLevel()
    {
        Assert.Equal(Display(Coll + "Coll((1, 2))"), Display(Coll + "Coll(((1, 2)))"));
        Assert.Equal("[(1, 2)]", Display(Coll + "Coll(((1, 2)))"));
        Assert.Equal("[((), 3)]", Display(Coll + "Coll((((), 3)))"));

        // Spread opens one level only: structured items of the opened value stay values.
        Assert.Equal("[(1, 2), (3, 4)]", Display(Coll + "Coll(((1, 2), (3, 4))*)"));
        Assert.Equal("[((1, 2), 3), 4]", Display(Coll + "Coll((((1, 2), 3), 4)*)"));
        Assert.Equal("[[1, 2], 3]", Display(Coll + "Coll(([1, 2], 3)*)"));
        Assert.Equal("[[1, 2], 3]", Display(Coll + "Coll([[1, 2], 3]*)"));
    }

    [Theory]
    [InlineData("(1, 2)")]
    [InlineData("()")]
    [InlineData("[]")]
    [InlineData("[1, 2]")]
    [InlineData("((1, 2), 3)")]
    public void Values_StayValues_ThroughReturnsStorageAndSelection(string value)
    {
        var definitions = Coll + "V = " + value + "\nId(x) = x\n" +
            "Stored = Id([V]*)\nTarget(*xs) = xs\nUse(xs) = Target\n";
        var one = "[" + value + "]";
        Assert.Equal(one, Display(definitions + "Coll([V]*)"));
        foreach (var expression in new[]
        {
            "V", "Id([V]*)", "Stored", "if(true, Id([V]*), 0)",
            "Coll([V]*):0", "first(Coll([V]*))", "last(Coll([V]*))",
            "[Id([V]*)]:0", "map([V], Id):0", "(Coll([V]*)*)",
        })
        {
            // map requires one emitted callback value; Id(()) emits zero.
            if (value == "()" && expression == "map([V], Id):0") continue;
            Assert.Equal(one, Display(definitions + "Coll(" + expression + ")"));
            Assert.Equal(one, Display(definitions + "(" + expression + ").Coll"));
            Assert.Equal("[" + value + ", 9]", Display(definitions + "Coll(" + expression + ", 9)"));
        }

        // Implicit forwarding of an ordinary parameter passes one argument; repeated
        // property reads exercise the cached value too.
        Assert.Equal(one, Display(definitions + "Use([V]*)"));
        Assert.Equal(one + "\n" + one, Display(definitions + "Coll(Stored), Coll(Stored)"));
        AssertStrategiesAgree(definitions + "Coll(Stored), Use([V]*), Coll(Stored, 9)");
    }

    // ── 5. Fixed parameters and mixed signatures ────────────────────────────

    [Fact]
    public void FixedParameters_BindTheirValuesUnchanged()
    {
        const string defs = "Id(x) = x\nAdd(x, y) = x + y\n";
        Assert.Equal("(1, 2)", Display(defs + "Id((1, 2))"));
        Assert.Equal("[1, 2]", Display(defs + "Id([1, 2])"));
        Assert.Equal("(1, 2)", Display(defs + "(1, 2).Id"));
        Assert.Equal("3", Display(defs + "Add((1, 2)*)"));
        Assert.Equal("3", Display(defs + "Add([1, 2]*)"));
        Assert.Equal("3", Display(defs + "(1, 2)*.Add"));
        Assert.Equal("3", Display(defs + "[1, 2]*.Add"));

        foreach (var call in new[] { "Add((1, 2))", "Add([1, 2])", "(1, 2).Add", "[1, 2].Add" })
        {
            var error = SourceProvenance.ParseValid(defs + call).ExpectEvaluationError<EvalError.ArityMismatch>();
            Assert.Equal(2, error.Expected);
            Assert.Equal(1, error.Actual);
        }
    }

    private const string MixedDefinitions =
        "WithHead(x, *rest) = (x, rest)\nWithTail(*rest, y) = (rest, y)\nMiddle(x, *middle, y) = (x, middle, y)\n";

    [Theory]
    // WithHead(x, *rest) — the prefix allocates first; the collector collects the rest exactly.
    [InlineData("WithHead(0, (1, 2))", "(0, [(1, 2)])")]
    [InlineData("WithHead(0, [1, 2])", "(0, [[1, 2]])")]
    [InlineData("WithHead(0, (1, 2)*)", "(0, [1, 2])")]
    [InlineData("WithHead(0, [1, 2]*)", "(0, [1, 2])")]
    [InlineData("WithHead(0, 7)", "(0, [7])")]
    [InlineData("WithHead(0, ())", "(0, [()])")]
    [InlineData("WithHead(0, [])", "(0, [[]])")]
    [InlineData("WithHead(0, ((1, 2), 3))", "(0, [((1, 2), 3)])")]
    [InlineData("WithHead(0, (1, 2), 3)", "(0, [(1, 2), 3])")]
    [InlineData("WithHead(0)", "(0, [])")]
    [InlineData("WithHead((1, 2))", "((1, 2), [])")]
    [InlineData("WithHead(0, [(1, 2)]*)", "(0, [(1, 2)])")]
    // WithTail(*rest, y) — the suffix allocates first.
    [InlineData("WithTail((1, 2), 9)", "([(1, 2)], 9)")]
    [InlineData("WithTail([1, 2], 9)", "([[1, 2]], 9)")]
    [InlineData("WithTail((1, 2)*, 9)", "([1, 2], 9)")]
    [InlineData("WithTail(7, 9)", "([7], 9)")]
    [InlineData("WithTail((), 9)", "([()], 9)")]
    [InlineData("WithTail([], 9)", "([[]], 9)")]
    [InlineData("WithTail((1, 2), 3, 9)", "([(1, 2), 3], 9)")]
    [InlineData("WithTail((1, 2))", "([], (1, 2))")]
    [InlineData("WithTail((1, 2)*)", "([1], 2)")]
    // Middle(x, *middle, y) — both fixed ends allocate first.
    [InlineData("Middle(0, (1, 2), 9)", "(0, [(1, 2)], 9)")]
    [InlineData("Middle(0, [1, 2], 9)", "(0, [[1, 2]], 9)")]
    [InlineData("Middle(0, (1, 2), 3, 9)", "(0, [(1, 2), 3], 9)")]
    [InlineData("Middle(0, [1, 2], 3, 9)", "(0, [[1, 2], 3], 9)")]
    [InlineData("Middle(0, [1, 2]*, 9)", "(0, [1, 2], 9)")]
    [InlineData("Middle(0, 9)", "(0, [], 9)")]
    [InlineData("Middle(0, (), 9)", "(0, [()], 9)")]
    [InlineData("Middle(0, [], 9)", "(0, [[]], 9)")]
    [InlineData("Middle(0, ((1, 2), 3), 9)", "(0, [((1, 2), 3)], 9)")]
    [InlineData("Middle((1, 2)*)", "(1, [], 2)")]
    public void MixedSignatures_CollectTheirSegmentExactly(string call, string expected)
    {
        Assert.Equal(expected, Display(MixedDefinitions + call));
        AssertStrategiesAgree(MixedDefinitions + call);

        // The dotted spelling of the same call: the first argument becomes the receiver.
        var open = call.IndexOf('(');
        var inner = call[(open + 1)..^1];
        if (inner.Length > 0)
        {
            var (receiver, rest) = SplitFirstArgument(inner);
            var callee = call[..open];
            Assert.Equal(expected, Display(MixedDefinitions + receiver + "." + callee + (rest is null ? "" : "(" + rest + ")")));
        }
    }

    [Theory]
    [InlineData("WithTail()", 1, 0)]
    [InlineData("WithHead()", 1, 0)]
    [InlineData("Middle()", 2, 0)]
    [InlineData("Middle((1, 2))", 2, 1)]
    [InlineData("Middle(())", 2, 1)]
    [InlineData("Middle([1, 2])", 2, 1)]
    [InlineData("Middle([1, 2, 3, 4])", 2, 1)]
    public void Arity_CountsSuppliedItems_NeverAValuesElementCount(string call, int expectedMinimum, int actual)
    {
        var error = SourceProvenance.ParseValid(MixedDefinitions + call)
            .ExpectEvaluationError<EvalError.VariadicArityMismatch>();
        Assert.Equal(expectedMinimum, error.ExpectedMinimum);
        Assert.Equal(actual, error.Actual);
    }

    // ── 6. Explicit structural patterns remain the openers ──────────────────

    [Theory]
    [InlineData("Pair((1, 2))", "(1, 2)")]
    [InlineData("Pair([1, 2])", "(1, 2)")]
    [InlineData("Pair(((1, 2), 3))", "((1, 2), 3)")]
    [InlineData("Pair([[1, 2], 3])", "([1, 2], 3)")]
    [InlineData("Parts((1, 2))", "[1, 2]")]
    [InlineData("Parts([1, 2])", "[1, 2]")]
    [InlineData("Parts(())", "[]")]
    [InlineData("Parts([])", "[]")]
    [InlineData("Parts(((1, 2), 3))", "[(1, 2), 3]")]
    [InlineData("Parts([[1, 2], 3])", "[[1, 2], 3]")]
    [InlineData("Parts(7)", "[7]")]
    [InlineData("HeadTail((1, 2))", "(1, [2])")]
    [InlineData("HeadTail([1, 2])", "(1, [2])")]
    [InlineData("HeadTail(((1, 2), 3))", "((1, 2), [3])")]
    [InlineData("HeadTail([[1, 2], 3])", "([1, 2], [3])")]
    [InlineData("HeadTail(7)", "(7, [])")]
    public void StructuralPatterns_OpenSequencesAndListsAlike(string call, string expected)
    {
        const string defs = "Pair((x, y)) = (x, y)\nParts((*xs)) = xs\nHeadTail((x, *xs)) = (x, xs)\n";
        Assert.Equal(expected, Display(defs + call));
        // The callback spelling binds exactly like the direct call.
        Assert.Equal("[" + expected + "]", Display(defs + "map([" + call[(call.IndexOf('(') + 1)..^1] + "], " + call[..call.IndexOf('(')] + ")"));
        AssertStrategiesAgree(defs + call);
    }

    [Theory]
    [InlineData("Pair(())")]
    [InlineData("Pair([])")]
    [InlineData("Pair(7)")]
    [InlineData("HeadTail(())")]
    [InlineData("HeadTail([])")]
    public void StructuralPatterns_RejectTooFewOpenedItems(string call)
    {
        const string defs = "Pair((x, y)) = (x, y)\nHeadTail((x, *xs)) = (x, xs)\n";
        Assert.Equal(KatLangErrorCode.ArityMismatch, FailureCode(defs + call));
    }

    // ── 7. Callbacks: each element is ONE ordinary argument ─────────────────

    private const string CallbackDefinitions =
        "Only(*xs) = xs\nCnt(*xs) = xs.count\nId(x) = x\nAdd(x, y) = x + y\n" +
        "AddPair((x, y)) = x + y\nNested((*xs)) = xs\nRest(a, *rest) = rest\n";

    [Fact]
    public void Callbacks_RequiredRelationships()
    {
        Assert.Equal(KatLangErrorCode.ArityMismatch, FailureCode(CallbackDefinitions + "map([(1, 2)], Add)"));
        Assert.Equal(KatLangErrorCode.ArityMismatch, FailureCode(CallbackDefinitions + "map([[1, 2]], Add)"));
        Assert.Equal("[3]", Display(CallbackDefinitions + "map([(1, 2)], AddPair)"));
        Assert.Equal("[3]", Display(CallbackDefinitions + "map([[1, 2]], AddPair)"));
        Assert.Equal("[1]", Display(CallbackDefinitions + "map([(1, 2)], Cnt)"));
        Assert.Equal("[1]", Display(CallbackDefinitions + "map([[1, 2]], Cnt)"));
        Assert.Equal("[[(1, 2)], [[3, 4]]]", Display(CallbackDefinitions + "((1, 2), [3, 4]).map(Only)"));
        Assert.Equal("[[1, 2], [3, 4]]", Display(CallbackDefinitions + "((1, 2), [3, 4]).map(Nested)"));
        Assert.Equal("[[], []]", Display(CallbackDefinitions + "((1, (2, 3)), (4, 5)).map(Rest)"));
        AssertStrategiesAgree(CallbackDefinitions + "map([(1, 2)], AddPair), map([[1, 2]], Cnt), ((1, 2), [3, 4]).map(Only)");
    }

    public static TheoryData<string, string> CallbackCells()
    {
        var data = new TheoryData<string, string>();
        foreach (var element in new[] { "1", "()", "[]", "(1, 2)", "[1, 2]", "((1, 2), 3)", "[[1, 2], 3]" })
            foreach (var callee in new[] { "Only", "Cnt", "Id", "Add", "AddPair", "Nested", "Rest" })
                data.Add(element, callee);
        return data;
    }

    /// <summary>
    /// THE CALLBACK LAW, metamorphically: for every element `E` and callee `F`,
    /// `map([E], F)` is the list literal `[F(E)]` — the callback binds exactly as the
    /// direct call — and the two fail together with the same error code. The one
    /// independent difference is map's own single-value RESULT contract: a transform
    /// returning `()` is no single element.
    /// </summary>
    [Theory]
    [MemberData(nameof(CallbackCells))]
    public void CallbackBinding_IsTheOrdinaryCall(string element, string callee)
    {
        var mapped = Outcome(CallbackDefinitions + "map([" + element + "], " + callee + ")");
        var direct = Outcome(CallbackDefinitions + "[" + callee + "(" + element + ")]");
        if (direct == "ok [()]")
            SourceProvenance.ParseValid(CallbackDefinitions + "map([" + element + "], " + callee + ")")
                .ExpectEvaluationError<EvalError.BadArity>();
        else
            Assert.Equal(direct, mapped);

        // filter binds its predicate like the call too: with an always-true predicate
        // shaped like `F`, the element is kept exactly when `F(E)` binds.
        var keep = callee + "Keep";
        var keepDefinitions = CallbackDefinitions + KeepPredicate(callee, keep);
        var filtered = Outcome(keepDefinitions + "filter([" + element + "], " + keep + ")");
        var directKeep = Outcome(keepDefinitions + keep + "(" + element + ")");
        if (directKeep.StartsWith("ok ", StringComparison.Ordinal))
            Assert.Equal(Outcome("[" + element + "]"), filtered);
        else
            Assert.Equal(directKeep, filtered);
    }

    private static string KeepPredicate(string callee, string name) => callee switch
    {
        "Only" or "Cnt" => name + "(*xs) = true\n",
        "Id" => name + "(x) = true\n",
        "Add" => name + "(x, y) = true\n",
        "AddPair" => name + "((x, y)) = true\n",
        "Nested" => name + "((*xs)) = true\n",
        "Rest" => name + "(a, *rest) = true\n",
        _ => throw new ArgumentOutOfRangeException(nameof(callee)),
    };

    [Fact]
    public void FilterPredicates_ReceiveOneArgument()
    {
        const string defs = "IsPair(*xs) = xs.count == 2\nIsPairValue(x) = x.count == 2\n";
        Assert.Equal("[]", Display(defs + "filter([(1, 2)], IsPair)"));
        Assert.Equal("[]", Display(defs + "filter([[1, 2]], IsPair)"));
        Assert.Equal("[(1, 2)]", Display(defs + "filter([(1, 2)], IsPairValue)"));
        Assert.Equal("[[1, 2]]", Display(defs + "filter([[1, 2]], IsPairValue)"));
        AssertStrategiesAgree(defs + "filter([(1, 2), [1, 2], 5], IsPair), filter([(1, 2), [1, 2], 5], IsPairValue)");
    }

    [Fact]
    public void FilterCountFusion_BindsCollectingPredicates_LikeTheGenericPath()
    {
        const string source = "P(*xs) = xs.count == 2\nQ(x) = x.count == 2\n((1, 2), 3, (4, 5), [6, 7]).filter(P).count";
        var sequence = new SequencePipelineDiagnostics();
        var (fused, _) = Evaluator.RunCountedObserved(AsyncEvaluationHarness.Ast(source), sequenceDiagnostics: sequence);
        var (generic, _) = Evaluator.RunCountedObserved(AsyncEvaluationHarness.Ast(source), enableOptimizations: false);
        Assert.True(fused.IsOk, fused.IsError ? fused.Error.ToString() : "");
        // Every element is ONE argument, so the collecting predicate never sees two.
        Assert.Equal("0", Assert.IsType<Result.Atom>(fused.Value.Value).Value.ToString());
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(generic), AsyncEvaluationHarness.NeutralOf(fused));
        Assert.Equal(1, sequence.GetSnapshot().FilterCountFusionHits);

        const string fixedSource = "Q(x) = x.count == 2\n((1, 2), 3, (4, 5), [6, 7]).filter(Q).count";
        Assert.Equal("3", Display(fixedSource));
        AssertStrategiesAgree(fixedSource);
    }

    // ── 8. Reducers: the reduce step is an ordinary two-argument callback ───

    private const string ReducerDefinitions =
        "Fixed(x, acc) = [x, acc]\nAccColl(x, *acc) = [x, acc]\nBoth(*xs) = xs\n" +
        "ItemColl(*items, acc) = [items, acc]\nAccPat(x, (a, *rest)) = [x, a, rest]\n" +
        "ItemPat((p, *q), acc) = [p, q, acc]\n";

    public static TheoryData<string, string, string> ReducerCells()
    {
        var data = new TheoryData<string, string, string>();
        foreach (var reducer in new[] { "Fixed", "AccColl", "Both", "ItemColl", "AccPat", "ItemPat" })
            foreach (var item in new[] { "7", "(1, 2)", "[1, 2]", "()", "[]" })
                foreach (var accumulator in new[] { "0", "(1, 2)", "[1, 2]", "()", "[]" })
                    data.Add(reducer, item, accumulator);
        return data;
    }

    /// <summary>
    /// `reduce([I], R, A)` is `R(I, A)` — the element and the accumulator are two
    /// ordinary arguments, each ONE value — for every reducer shape, and the generic,
    /// planned, and async strategies agree.
    /// </summary>
    [Theory]
    [MemberData(nameof(ReducerCells))]
    public void ReduceStep_IsTheOrdinaryTwoArgumentCall(string reducer, string item, string accumulator)
    {
        var reduced = ReducerDefinitions + "reduce([" + item + "], " + reducer + ", " + accumulator + ")";
        Assert.Equal(
            Outcome(ReducerDefinitions + reducer + "(" + item + ", " + accumulator + ")"),
            Outcome(reduced));
        AssertStrategiesAgree(reduced);
    }

    [Fact]
    public void ReducerAccumulator_IsOneValue_OpenedOnlyByAnExplicitPattern()
    {
        const string defs = "Acc(x, *acc) = acc\nSum2(x, (a, b)) = (a + x, b + 1)\nApp(item, *hist) = (hist*, item)\n";
        Assert.Equal("[(1, 2)]", Display(defs + "reduce([9], Acc, (1, 2))"));
        Assert.Equal("[[1, 2]]", Display(defs + "reduce([9], Acc, [1, 2])"));
        Assert.Equal("[()]", Display(defs + "reduce([9], Acc, ())"));
        Assert.Equal("[[]]", Display(defs + "reduce([9], Acc, [])"));
        Assert.Equal("[((1, 2), 3)]", Display(defs + "reduce([9], Acc, ((1, 2), 3))"));
        Assert.Equal("(6, 3)", Display(defs + "reduce([1, 2, 3], Sum2, (0, 0))"));
        Assert.Equal("(6, 3)", Display(defs + "reduce([1, 2, 3], Sum2, [0, 0])"));
        Assert.Equal("((1, 2), 9)", Display(defs + "reduce([9], App, (1, 2))"));
        AssertStrategiesAgree(defs + "reduce([1, 2, 3], Sum2, (0, 0)), reduce([9], Acc, (1, 2))");
    }

    [Theory]
    [InlineData("(1, 2)", "[(1, 2)]")]
    [InlineData("()", "[()]")]
    [InlineData("[]", "[[]]")]
    [InlineData("[1, 2]", "[[1, 2]]")]
    [InlineData("((1, 2), 3)", "[((1, 2), 3)]")]
    public void ReducerElementSideCollector_ReceivesOneArgument(string item, string expected)
    {
        var source = "R(*items, acc) = items\nreduce([" + item + "], R, 99)";
        Assert.Equal(expected, Display(source));
        AssertStrategiesAgree(source);
    }

    // ── 9. Loops keep their established state slots ─────────────────────────

    [Theory]
    [InlineData("repeat(Id, 1, 7)", "7")]
    [InlineData("repeat(Id, 1, (1, 2))", "(1, 2)")]
    [InlineData("repeat(Id, 1, [1, 2])", "[1, 2]")]
    [InlineData("repeat(Swap, 1, (1, 2))", "(2, 1)")]
    [InlineData("repeat(Swap, 1, [1, 2])", "(2, 1)")]
    [InlineData("repeat(Swap, 2, (1, 2))", "(1, 2)")]
    [InlineData("repeat(Fib, 5, 0, 1)", "5\n8")]
    [InlineData("repeat(Cnt, 1, (1, 2))", "1")]
    [InlineData("repeat(Cnt, 1, [1, 2])", "1")]
    [InlineData("repeat(Cnt, 1, 1, 2)", "2")]
    [InlineData("repeat(Cnt, 1, (1, 2)*)", "2")]
    [InlineData("while(W, 0, (1, 2))", "1\n1")]
    [InlineData("while(W, 0, [1, 2])", "1\n1")]
    [InlineData("while(W, 0, 1, 2)", "1\n2")]
    public void LoopStateSlots_AreEstablishedItems(string call, string expected)
    {
        // A lone multi-slot loop result displays one root row per state slot.
        const string defs = "Id(x) = x\nSwap((a, b)) = (b, a)\nFib(a, b) = b, a + b\nCnt(*xs) = xs.count\n" +
            "W(n, *xs) = n + 1, xs.count, n < 1\n";
        Assert.Equal(expected, Display(defs + call));
        AssertStrategiesAgree(defs + call);
    }

    [Fact]
    public void LoopStateSlots_KeepTheirItems_AndCollectingStepsDeclinePlanning()
    {
        const string source = "Step(*xs) = xs.count\nrepeat(Step, 1, (1, 2)), repeat(Step, 1, 1, 2), repeat(Step, 1, [1, 2])";
        Assert.Equal("1\n2\n1", Display(source));
        var ast = AsyncEvaluationHarness.Ast(source);
        var loop = new LoopOptimizationDiagnostics();
        var (planned, _) = Evaluator.RunCountedObserved(ast, loopDiagnostics: loop);
        var (generic, _) = Evaluator.RunCountedObserved(ast, enableOptimizations: false);
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(generic), AsyncEvaluationHarness.NeutralOf(planned));

        Assert.Equal(0, loop.OptimizedLoopHits);
        Assert.Equal(3, loop.FallbackReasons["variadic loop step"]);

        const string mixed = "Step(*xs, last) = xs.count, last\nrepeat(Step, 1, (1, 2), 3), repeat(Step, 1, (1, 2), 3, 4)";
        Assert.Equal("(1, 3)\n(2, 4)", Display(mixed));
    }

    [Theory]
    [InlineData("(1, 2)", "[(1, 2)]\n2")]
    [InlineData("()", "[()]\n2")]
    [InlineData("[1, 2]", "[[1, 2]]\n2")]
    public void CollectorInLoopTemp_BindsOneArgument(string value, string expected)
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

    // ── 10. Dot-call is ordinary receiver injection ─────────────────────────

    public static TheoryData<string, string, string> DotCallCells()
    {
        var data = new TheoryData<string, string, string>();
        foreach (var receiver in new[] { "7", "(1, 2)", "[1, 2]", "()", "[]", "((1, 2), 3)", "[[1, 2], 3]" })
        {
            data.Add(receiver, "Fixed2", "(9)");
            data.Add(receiver, "Fixed1", "");
            data.Add(receiver, "Coll", "");
            data.Add(receiver, "Coll", "(9)");
            data.Add(receiver, "WithHead", "(9)");
            data.Add(receiver, "WithTail", "(9)");
            data.Add(receiver, "WithTail", "");
            data.Add(receiver, "Middle", "(8, 9)");
            data.Add(receiver, "map", "(Only)");
        }

        return data;
    }

    /// <summary>`R.F(args)` is `F(R, args)` and `R*.F(args)` is `F(R*, args)` for every callee shape.</summary>
    [Theory]
    [MemberData(nameof(DotCallCells))]
    public void DotCall_IsOrdinaryReceiverInjection(string receiver, string callee, string arguments)
    {
        const string defs = Coll + MixedDefinitions + "Fixed2(a, b) = (a, b)\nFixed1(a) = [a]\nOnly(*xs) = xs\n";
        var rest = arguments.Length == 0 ? "" : ", " + arguments[1..^1];
        Assert.Equal(
            Outcome(defs + callee + "(" + receiver + rest + ")"),
            Outcome(defs + receiver + "." + callee + arguments));
        Assert.Equal(
            Outcome(defs + callee + "(" + receiver + "*" + rest + ")"),
            Outcome(defs + receiver + "*." + callee + arguments));
    }

    // ── 11. Selection chooses a value ───────────────────────────────────────

    [Fact]
    public void Selection_FeedsEveryConsumerAsOneValue()
    {
        const string defs = Coll + "A = ((1, 2), 3)\nL = [[1, 2], 3]\nId(x) = x\nAdd(x, y) = x + y\nAddPair((x, y)) = x + y\n";
        foreach (var (selection, value) in new[]
        {
            ("A:0", "(1, 2)"), ("first(A)", "(1, 2)"), ("last((3, A:0))", "(1, 2)"),
            ("L:0", "[1, 2]"), ("first(L)", "[1, 2]"),
        })
        {
            Assert.Equal(value, Display(defs + selection));
            Assert.Equal(value, Display(defs + "Id(" + selection + ")"));
            Assert.Equal("[" + value + "]", Display(defs + "Coll(" + selection + ")"));
            Assert.Equal("[" + value + "]", Display(defs + "(" + selection + ").Coll"));
            Assert.Equal("[" + value + "]", Display(defs + "X = " + selection + "\nColl(X)"));
            Assert.Equal("[1, 2]", Display(defs + "Coll((" + selection + ")*)"));
            Assert.Equal("[1, 2]", Display(defs + "(" + selection + ")*.Coll"));
            Assert.Equal("3", Display(defs + "AddPair(" + selection + ")"));
            Assert.Equal("3", Display(defs + "Add((" + selection + ")*)"));
            Assert.Equal("[3]", Display(defs + "map([" + selection + "], AddPair)"));
            Assert.Equal(KatLangErrorCode.ArityMismatch, FailureCode(defs + "Add(" + selection + ")"));
        }

        // first(A) ≡ A:0 and last(A) ≡ A:(A.count - 1) through every consumer.
        foreach (var consumer in new[] { "Coll({0})", "({0}).Coll", "Coll(({0})*)", "AddPair({0})", "map([{0}], Coll)" })
        {
            Assert.Equal(Display(defs + string.Format(consumer, "A:0")), Display(defs + string.Format(consumer, "first(A)")));
            Assert.Equal(Display(defs + string.Format(consumer, "L:0")), Display(defs + string.Format(consumer, "first(L)")));
        }

        Assert.Equal(Display(defs + "Coll(A:(A.count - 1))"), Display(defs + "Coll(last(A))"));
        AssertStrategiesAgree(defs + "Coll(A:0), Coll(first(A)), Coll((A:0)*), map([first(L)], AddPair)");
    }

    // ── 12. Forwarding, aliases, and nested capture ─────────────────────────

    [Theory]
    [InlineData("")]
    [InlineData("1")]
    [InlineData("()")]
    [InlineData("[]")]
    [InlineData("(1, 2)")]
    [InlineData("[1, 2]")]
    [InlineData("[(1, 2)]*")]
    [InlineData("[()]*")]
    [InlineData("[[1, 2]]")]
    [InlineData("((1, 2), 3)")]
    [InlineData("[[1, 2], 3]")]
    [InlineData("1, (1, 2), [], ()")]
    public void ForwardingLaw_SpreadOfCollectReconstructsTheSupply(string supply)
    {
        const string defs = Coll + "Target(*xs) = xs\nForward(*xs) = Target(xs*)\nForward2(*xs) = Forward(xs*)\n";
        var direct = Display(defs + "Coll(" + supply + ")");
        Assert.Equal(direct, Display(defs + "Target(" + supply + ")"));
        Assert.Equal(direct, Display(defs + "Forward(" + supply + ")"));
        Assert.Equal(direct, Display(defs + "Forward2(" + supply + ")"));
        AssertStrategiesAgree(defs + "Forward2(" + supply + ")");
    }

    [Fact]
    public void AliasesAndForwarding_KeepTheCallbackLaw()
    {
        const string defs =
            "Cnt(*xs) = xs.count\nAlias = Cnt\nApply(f, xs) = map(xs, f)\n" +
            "Forward(g, xs) = Apply(g, xs)\nForward2(h, xs) = Forward(h, xs)\n" +
            "ApplyBlock(f, xs) = { map(xs, f) }\n";
        foreach (var input in new[] { "[(10, 7), 20]", "[[10, 7], 20]" })
        {
            foreach (var call in new[]
            {
                "map(" + input + ", Cnt)", "map(" + input + ", Alias)", "Apply(Cnt, " + input + ")",
                "Apply(Alias, " + input + ")", "Forward(Alias, " + input + ")", "Forward2(Alias, " + input + ")",
                "Forward2(Cnt, " + input + ")", "ApplyBlock(Alias, " + input + ")", input + ".map(Alias)",
            })
            {
                Assert.Equal("[1, 1]", Display(defs + call));
            }

            AssertStrategiesAgree(defs + "Forward2(Alias, " + input + ")");
        }

        Assert.Equal("1", Display(defs + "Cnt((10, 7))"));
        Assert.Equal("1", Display(defs + "Cnt([10, 7])"));
        Assert.Equal("1", Display(defs + "Alias([10, 7])"));
        Assert.Equal("2", Display(defs + "Cnt((10, 7)*)"));
        Assert.Equal("2", Display(defs + "Cnt([10, 7]*)"));
        Assert.Equal("2", Display(defs + "Alias([10, 7]*)"));
    }

    // ── 13. Deconstruction and builtins keep their explicit structure views ──

    [Fact]
    public void Deconstruction_KeepsItsOwnOneLevelOpeningRule()
    {
        // Deconstruction is explicit structural syntax: it opens one lone sequence or
        // list boundary of its shared right-hand side, and its collecting target collects
        // the matched items exactly.
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

    // ── 14. Async: a genuinely suspended run follows the same binding law ────

    [Theory]
    [InlineData("Coll(Pair())", "[(1, 2)]")]
    [InlineData("Pair().Coll", "[(1, 2)]")]
    [InlineData("Coll(Pair(), 3)", "[(1, 2), 3]")]
    [InlineData("Pair().Coll(3)", "[(1, 2), 3]")]
    [InlineData("Coll(Pair()*)", "[1, 2]")]
    [InlineData("F(Pair(), 3)", "([(1, 2)], 3)")]
    [InlineData("F(Pair(), 3, 4)", "([(1, 2), 3], 4)")]
    [InlineData("G(1, Pair())", "(1, [(1, 2)])")]
    [InlineData("G(1, Pair(), 3)", "(1, [(1, 2), 3])")]
    [InlineData("Coll(Empty())", "[()]")]
    [InlineData("Coll(Empty(), 3)", "[(), 3]")]
    [InlineData("Coll(Items())", "[[1, 2]]")]
    [InlineData("Coll(Items()*)", "[1, 2]")]
    [InlineData("map([Pair()], Coll)", "[[(1, 2)]]")]
    [InlineData("reduce([9], Acc, Pair())", "[(1, 2)]")]
    public async Task SuspendedAsyncRun_BindsExactlyLikeTheSynchronousRun(string expression, string expected)
    {
        const string definitions = Coll + "F(*xs, z) = xs, z\nG(x, *rest) = x, rest\nAcc(x, *acc) = acc\n";
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
            // `first(Middle())` is the one value `(1, 2)`; `Middle()*` supplies the one
            // established item `(1, 2)`: both are ONE collected item.
            var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source, syncOptions));
            Assert.Equal("[(1, 2)]", success.ToDisplayString());
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
