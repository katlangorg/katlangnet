namespace KatLang.Tests;

/// <summary>
/// STRUCTURAL PATTERN DELIMITERS SELECT THE VALUE KIND THEY DESTRUCTURE (September 2026). A
/// parenthesized structural pattern <c>(p1, …, pn)</c> matches SEQUENCE values only and a
/// bracketed structural pattern <c>[p1, …, pn]</c> matches LIST values only; neither
/// destructures the other kind, and no scalar is a one-item structure. A bare binder is the
/// only pattern that takes a value whole. The same kind law holds for ordinary parameter
/// patterns, callbacks and clause families — they differ only in what a mismatch does (an
/// ordinary binding fails with a <c>TypeMismatch</c> for the wrong kind and an
/// <c>ArityMismatch</c> for the wrong length; a family tries its next clause).
///
/// <para>Evidence: a value × pattern matrix run on the six execution routes of
/// <see cref="RepeatedNameConstraintTests.OnEveryRouteAsync"/> against an independent kind/length
/// oracle; exact bindings for every accepted cell; the callback spelling <c>map([v], P)</c>
/// against the direct call <c>P(v)</c>; a clause family with the same head against the ordinary
/// binding; nested mixed patterns; and the empty structures. Lean evaluates the same laws in
/// <c>CoreTests/StructuralPatterns.lean</c> and <c>KatLangArityLaws.lean</c>.</para>
/// </summary>
public class StructuralPatternKindTests
{
    private enum Kind { Scalar, Sequence, List }

    /// <summary>A test value: its source spelling, its kind, and its element count.</summary>
    private sealed record Value(string Source, Kind Kind, int Count);

    /// <summary>
    /// A structural pattern under test: its head spelling, the kind it selects (null for a bare
    /// binder), its fixed item count, whether it holds a collector, and a body that returns its
    /// bindings as one list.
    /// </summary>
    private sealed record PatternCase(string Head, Kind? Kind, int Fixed, bool Collects, string Body);

    private static readonly Value[] Values =
    [
        new("7", Kind.Scalar, 0),
        new("()", Kind.Sequence, 0),
        new("(1, 2)", Kind.Sequence, 2),
        new("(1, 2, 3)", Kind.Sequence, 3),
        new("[]", Kind.List, 0),
        new("[7]", Kind.List, 1),
        new("[1, 2]", Kind.List, 2),
        new("[[7]]", Kind.List, 1),
        new("[(1, 2)]", Kind.List, 1),
        new("[()]", Kind.List, 1),
        new("[[]]", Kind.List, 1),
        new("([1], 2)", Kind.Sequence, 2),
        new("'s'", Kind.Scalar, 0),
        new("true", Kind.Scalar, 0),
    ];

    private static readonly PatternCase[] Patterns =
    [
        new("x", null, 0, false, "[x]"),
        new("()", Kind.Sequence, 0, false, "[0]"),
        new("(x, y)", Kind.Sequence, 2, false, "[x, y]"),
        new("(*xs)", Kind.Sequence, 0, true, "[xs]"),
        new("(x, *rest)", Kind.Sequence, 1, true, "[x, rest]"),
        new("(x, *middle, z)", Kind.Sequence, 2, true, "[x, middle, z]"),
        new("[]", Kind.List, 0, false, "[0]"),
        new("[x]", Kind.List, 1, false, "[x]"),
        new("[x, y]", Kind.List, 2, false, "[x, y]"),
        new("[*xs]", Kind.List, 0, true, "[xs]"),
        new("[x, *rest]", Kind.List, 1, true, "[x, rest]"),
        new("[x, *middle, z]", Kind.List, 2, true, "[x, middle, z]"),
    ];

    /// <summary>
    /// The independent oracle: the outcome CATEGORY the kind law predicts — <c>ok</c>, the
    /// kind mismatch <c>err TypeMismatch</c>, or the length mismatch <c>err ArityMismatch</c>.
    /// </summary>
    private static string Predict(PatternCase pattern, Value value)
    {
        if (pattern.Kind is null)
            return "ok";
        if (pattern.Kind != value.Kind)
            return "err TypeMismatch";
        var fits = pattern.Collects ? value.Count >= pattern.Fixed : value.Count == pattern.Fixed;
        return fits ? "ok" : "err ArityMismatch";
    }

    private static string Category(string outcome)
        => outcome.StartsWith("ok ", StringComparison.Ordinal)
            ? "ok"
            : outcome[..outcome.IndexOf(':', StringComparison.Ordinal)];

    public static TheoryData<int, int> Matrix()
    {
        var data = new TheoryData<int, int>();
        for (var p = 0; p < Patterns.Length; p++)
            for (var v = 0; v < Values.Length; v++)
                data.Add(p, v);
        return data;
    }

    [Theory]
    [MemberData(nameof(Matrix))]
    public async Task OrdinaryPattern_AcceptsExactlyItsOwnKindAndLength_OnEveryRoute(int patternIndex, int valueIndex)
    {
        var pattern = Patterns[patternIndex];
        var value = Values[valueIndex];
        var observation = await RepeatedNameConstraintTests.OnEveryRouteAsync(
            $"P({pattern.Head}) = {pattern.Body}\nP({value.Source})");
        Assert.True(
            Predict(pattern, value) == Category(observation.Outcome),
            $"P({pattern.Head}) on {value.Source}: expected {Predict(pattern, value)}, got {observation.Outcome}");
    }

    [Theory]
    [MemberData(nameof(Matrix))]
    public async Task CallbackElement_BindsExactlyLikeTheDirectCall(int patternIndex, int valueIndex)
    {
        var pattern = Patterns[patternIndex];
        var value = Values[valueIndex];
        var declaration = $"P({pattern.Head}) = {pattern.Body}\n";
        var direct = await RepeatedNameConstraintTests.OnEveryRouteAsync($"{declaration}P({value.Source})");
        var viaMap = await RepeatedNameConstraintTests.OnEveryRouteAsync($"{declaration}map([{value.Source}], P)");
        if (Category(direct.Outcome) == "ok")
            Assert.Equal($"ok L[{direct.Outcome[3..]}]", viaMap.Outcome);
        else
            Assert.Equal(Category(direct.Outcome), Category(viaMap.Outcome));
    }

    public static TheoryData<int, int> FamilyMatrix()
    {
        // Families have no collecting binders (InvalidCollectingBinding) and a bare-binder
        // clause would duplicate the catch-all, so the family matrix takes the fixed
        // structural patterns.
        var data = new TheoryData<int, int>();
        for (var p = 0; p < Patterns.Length; p++)
        {
            if (Patterns[p].Kind is null || Patterns[p].Collects)
                continue;
            for (var v = 0; v < Values.Length; v++)
                data.Add(p, v);
        }

        return data;
    }

    [Theory]
    [MemberData(nameof(FamilyMatrix))]
    public async Task ClauseFamily_SelectsTheClauseExactlyWhenTheOrdinaryPatternWouldBind(int patternIndex, int valueIndex)
    {
        var pattern = Patterns[patternIndex];
        var value = Values[valueIndex];
        var family = await RepeatedNameConstraintTests.OnEveryRouteAsync(
            $"F({pattern.Head}) = 'hit'\nF(other) = 'miss'\nF({value.Source})");
        var expected = Predict(pattern, value) == "ok" ? "ok 'hit'" : "ok 'miss'";
        Assert.True(expected == family.Outcome, $"F({pattern.Head}) on {value.Source}: expected {expected}, got {family.Outcome}");

        // Without the catch-all, a non-matching argument is the family's NoMatchingBranch —
        // never the ordinary binder's kind or length mismatch.
        var lone = await RepeatedNameConstraintTests.OnEveryRouteAsync(
            $"F({pattern.Head}) = 'hit'\nF('never') = 'never'\nF({value.Source})");
        Assert.Equal(
            Predict(pattern, value) == "ok" ? "ok" : "err NoMatchingBranch",
            Category(lone.Outcome));
    }

    public static TheoryData<string, string, string> Bindings => new()
    {
        // Bare binders take the whole value, whatever its kind.
        { "x", "[7]", "ok L[L[7]]" },
        { "x", "(1, 2)", "ok L[S[1, 2]]" },
        { "x", "7", "ok L[7]" },
        // Sequence patterns bind a sequence's elements; a collector collects an exact list.
        { "(x, y)", "(1, 2)", "ok L[1, 2]" },
        { "(x, y)", "([1], 2)", "ok L[L[1], 2]" },
        { "(*xs)", "()", "ok L[L[]]" },
        { "(*xs)", "(1, 2)", "ok L[L[1, 2]]" },
        { "(*xs)", "(1, 2, 3)", "ok L[L[1, 2, 3]]" },
        { "(x, *rest)", "(1, 2)", "ok L[1, L[2]]" },
        { "(x, *rest)", "(1, 2, 3)", "ok L[1, L[2, 3]]" },
        { "(x, *middle, z)", "(1, 2)", "ok L[1, L[], 2]" },
        { "(x, *middle, z)", "(1, 2, 3)", "ok L[1, L[2], 3]" },
        // List patterns keep every cardinality.
        { "[x]", "[7]", "ok L[7]" },
        { "[x]", "[[7]]", "ok L[L[7]]" },
        { "[x]", "[(1, 2)]", "ok L[S[1, 2]]" },
        { "[x]", "[()]", "ok L[S[]]" },
        { "[x]", "[[]]", "ok L[L[]]" },
        { "[x, y]", "[1, 2]", "ok L[1, 2]" },
        { "[*xs]", "[]", "ok L[L[]]" },
        { "[*xs]", "[7]", "ok L[L[7]]" },
        { "[*xs]", "[1, 2]", "ok L[L[1, 2]]" },
        { "[x, *rest]", "[7]", "ok L[7, L[]]" },
        { "[x, *rest]", "[1, 2]", "ok L[1, L[2]]" },
        { "[x, *middle, z]", "[1, 2]", "ok L[1, L[], 2]" },
        { "[*prefix, z]", "[1, 2, 3]", "ok L[L[1, 2], 3]" },
        { "[*prefix, z]", "[7]", "ok L[L[], 7]" },
        // The empty patterns.
        { "()", "()", "ok L[0]" },
        { "[]", "[]", "ok L[0]" },
    };

    [Theory]
    [MemberData(nameof(Bindings))]
    public async Task AcceptedPatterns_BindExactlyTheElements(string head, string value, string expected)
    {
        var body = head switch
        {
            "()" or "[]" => "[0]",
            _ => "[" + string.Join(", ", ParameterNames(head)) + "]",
        };
        var observation = await RepeatedNameConstraintTests.OnEveryRouteAsync($"P({head}) = {body}\nP({value})");
        Assert.Equal(expected, observation.Outcome);
    }

    private static IEnumerable<string> ParameterNames(string head)
        => head.Split([',', '(', ')', '[', ']', ' ', '*'], StringSplitOptions.RemoveEmptyEntries);

    [Fact]
    public async Task WrongKind_IsATypeMismatchNamingThePatternAndTheValue()
    {
        var sequence = await RepeatedNameConstraintTests.OnEveryRouteAsync("Add((x, y)) = x + y\nAdd([10, 20])");
        Assert.Equal(
            "err TypeMismatch: while evaluating call to Add: Type mismatch: sequence pattern `(x, y)` expects a sequence value, but received a list value with 2 elements: [10, 20]",
            sequence.Outcome);

        var list = await RepeatedNameConstraintTests.OnEveryRouteAsync("Single([x]) = x\nSingle(7)");
        Assert.Equal(
            "err TypeMismatch: while evaluating call to Single: Type mismatch: list pattern `[x]` expects a list value, but received numeric value 7",
            list.Outcome);

        // A right-kind value of the wrong length is the pattern's arity mismatch.
        var length = await RepeatedNameConstraintTests.OnEveryRouteAsync("Add((x, y)) = x + y\nAdd((1, 2, 3))");
        Assert.Equal(
            "err ArityMismatch: Sequence pattern `(x, y)` expects 2 elements, but received 3 elements.",
            length.Outcome);

        var listLength = await RepeatedNameConstraintTests.OnEveryRouteAsync("Pair([x, y]) = x + y\nPair([1])");
        Assert.Equal(
            "err ArityMismatch: List pattern `[x, y]` expects 2 elements, but received 1 element.",
            listLength.Outcome);
    }

    public static TheoryData<string, string, string> Nested => new()
    {
        // F(([x, y], z)): a two-element SEQUENCE whose first element is a two-element LIST.
        { "F(([x, y], z)) = x + y + z", "F(([10, 20], 30))", "ok 60" },
        { "F(([x, y], z)) = x + y + z", "F([[10, 20], 30])", "err TypeMismatch" },
        { "F(([x, y], z)) = x + y + z", "F(((10, 20), 30))", "err TypeMismatch" },
        { "F(([x, y], z)) = x + y + z", "F(([10], 30))", "err ArityMismatch" },
        // G([(x, y), z]): a two-element LIST whose first element is a two-element SEQUENCE.
        { "G([(x, y), z]) = x + y + z", "G([(1, 2), 3])", "ok 6" },
        { "G([(x, y), z]) = x + y + z", "G(((1, 2), 3))", "err TypeMismatch" },
        { "G([(x, y), z]) = x + y + z", "G([[1, 2], 3])", "err TypeMismatch" },
        // Collectors inside nested mixed patterns.
        { "H([(x, *r), *s]) = [x, r, s]", "H([(1, 2, 3), 4, 5])", "ok L[1, L[2, 3], L[4, 5]]" },
        { "H([(x, *r), *s]) = [x, r, s]", "H([(1, 2)])", "ok L[1, L[2], L[]]" },
        { "K(([*a], [*b])) = [a, b]", "K(([], [1]))", "ok L[L[], L[1]]" },
        { "K(([*a], [*b])) = [a, b]", "K(([1, 2], []))", "ok L[L[1, 2], L[]]" },
        // Nested empties.
        { "E([()]) = 1", "E([()])", "ok 1" },
        { "E([()]) = 1", "E([[]])", "err TypeMismatch" },
        { "E([[]]) = 1", "E([[]])", "ok 1" },
        { "E([[]]) = 1", "E([()])", "err TypeMismatch" },
        { "E(((), [])) = 1", "E(((), []))", "ok 1" },
        { "E(((), [])) = 1", "E(([], ()))", "err TypeMismatch" },
    };

    [Theory]
    [MemberData(nameof(Nested))]
    public async Task NestedStructuralPatterns_PreserveKindAtEveryLevel(string declaration, string call, string expected)
    {
        var observation = await RepeatedNameConstraintTests.OnEveryRouteAsync($"{declaration}\n{call}");
        Assert.Equal(expected, expected.StartsWith("ok ", StringComparison.Ordinal) ? observation.Outcome : Category(observation.Outcome));
    }

    [Fact]
    public async Task EmptyStructures_StayDistinct()
    {
        Assert.Equal("ok 1", (await RepeatedNameConstraintTests.OnEveryRouteAsync("F(()) = 1\nF(())")).Outcome);
        Assert.Equal("err TypeMismatch", Category((await RepeatedNameConstraintTests.OnEveryRouteAsync("F(()) = 1\nF([])")).Outcome));
        Assert.Equal("ok 1", (await RepeatedNameConstraintTests.OnEveryRouteAsync("F([]) = 1\nF([])")).Outcome);
        Assert.Equal("err TypeMismatch", Category((await RepeatedNameConstraintTests.OnEveryRouteAsync("F([]) = 1\nF(())")).Outcome));
        Assert.Equal("ok S[0, 1, 2]", (await RepeatedNameConstraintTests.OnEveryRouteAsync(
            "K(()) = 0\nK([]) = 1\nK(other) = 2\nK(()), K([]), K(7)")).Outcome);
    }

    [Fact]
    public async Task ASequencePatternHasNoOneItemValueToMatch()
    {
        // `(7)` IS 7 (VAL-03), so a one-item "sequence" never reaches a sequence pattern: the
        // collector-only `(*xs)` sees 0 or at least 2 elements, and a scalar is its kind mismatch.
        Assert.Equal("err TypeMismatch", Category((await RepeatedNameConstraintTests.OnEveryRouteAsync("C((*xs)) = xs\nC((7))")).Outcome));
        Assert.Equal("ok L[1, 2]", (await RepeatedNameConstraintTests.OnEveryRouteAsync("C((*xs)) = xs\nC((1, 2))")).Outcome);
        Assert.Equal("ok L[]", (await RepeatedNameConstraintTests.OnEveryRouteAsync("C((*xs)) = xs\nC(())")).Outcome);
        // The list collector sees every cardinality, one included.
        Assert.Equal("ok L[7]", (await RepeatedNameConstraintTests.OnEveryRouteAsync("L([*xs]) = xs\nL([7])")).Outcome);
    }

    [Fact]
    public async Task OuterCallArity_IsDistinctFromStructuralShape()
    {
        // F(x, y): two top-level parameters. F((x, y)): one sequence. F([x, y]): one list.
        Assert.Equal("ok 3", (await RepeatedNameConstraintTests.OnEveryRouteAsync("F(x, y) = x + y\nF(1, 2)")).Outcome);
        Assert.Equal("err ArityMismatch", Category((await RepeatedNameConstraintTests.OnEveryRouteAsync("F(x, y) = x + y\nF((1, 2))")).Outcome));
        Assert.Equal("ok 3", (await RepeatedNameConstraintTests.OnEveryRouteAsync("F((x, y)) = x + y\nF((1, 2))")).Outcome);
        Assert.Equal("err ArityMismatch", Category((await RepeatedNameConstraintTests.OnEveryRouteAsync("F((x, y)) = x + y\nF(1, 2)")).Outcome));
        Assert.Equal("ok 3", (await RepeatedNameConstraintTests.OnEveryRouteAsync("F([x, y]) = x + y\nF([1, 2])")).Outcome);
        Assert.Equal("err ArityMismatch", Category((await RepeatedNameConstraintTests.OnEveryRouteAsync("F([x, y]) = x + y\nF(1, 2)")).Outcome));
        // A spread supplies items to the TOP level only: `F((1, 2)*)` is `F(1, 2)`.
        Assert.Equal("ok 3", (await RepeatedNameConstraintTests.OnEveryRouteAsync("F(x, y) = x + y\nF((1, 2)*)")).Outcome);
    }

    [Fact]
    public async Task SingleStructuralClauses_AreOrdinaryAlgorithms()
    {
        // A single clause whose head holds only binders and structural patterns of either kind
        // is an ORDINARY algorithm: its parameters keep the algorithm channel.
        var single = SourceProvenance.ParseValid("Single([x]) = x\nPair((a, b)) = a + b\nSingle([7]), Pair((1, 2))");
        Assert.IsType<Algorithm.User>(single.Root.Properties.Single(static p => p.Name == "Single").Value);
        Assert.IsType<Algorithm.User>(single.Root.Properties.Single(static p => p.Name == "Pair").Value);
        var singleParameters = ((Algorithm.User)single.Root.Properties.Single(static p => p.Name == "Single").Value).ParameterPatterns;
        Assert.IsType<ListValueParameterPattern>(Assert.Single(singleParameters));

        // A literal anywhere, or a second clause, makes a family.
        var family = SourceProvenance.ParseValid("Kind([0]) = 'zero'\nKind([x]) = 'one'\nKind([0]), Kind([5])");
        Assert.IsType<Algorithm.Conditional>(family.Root.Properties.Single(static p => p.Name == "Kind").Value);
        Assert.Equal("ok S['zero', 'one']", (await RepeatedNameConstraintTests.OnEveryRouteAsync(
            "Kind([0]) = 'zero'\nKind([x]) = 'one'\nKind([0]), Kind([5])")).Outcome);
    }
}
