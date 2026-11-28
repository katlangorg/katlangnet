using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// COLLECTING BINDINGS INSIDE CLAUSE-FAMILY PATTERNS (Q-47, owner decision 2026-11-27). A clause
/// family has one fixed call arity; within any argument, a list or sequence pattern may contain
/// collecting bindings under the ordinary structural-pattern rules. <c>F([head, *rest])</c>
/// inspects one list argument and <c>F((head, *rest))</c> one sequence argument, in a single
/// literal-bearing clause and in a family of several clauses alike. A collector directly among a
/// family's call arguments (<c>F(head, *rest)</c>, <c>F(*xs)</c>) stays
/// <see cref="DiagnosticCode.InvalidCollectingBinding"/>, and the whole same-name group is
/// classified first, so a single literal-free clause keeps its top-level collecting parameter.
///
/// <para>Every expectation here is hand-written from the decision. Evaluated programs run on the
/// six execution routes of <see cref="RepeatedNameConstraintTests.OnEveryRouteAsync"/> (sync and
/// async engine, generic, optimized, forced async twin), which must agree on the outcome, the
/// error location and the host-call log. Lean evaluates the same programs in
/// <c>CoreTests/StructuralPatterns.lean</c> (guards 11–16) and the canonical cases are in
/// <c>conformance/features/clause-dispatch.json</c> and <c>structural-patterns.json</c>.</para>
/// </summary>
public class ClauseFamilyCollectingPatternTests
{
    private const string Tail = "Tail([]) = []\nTail([head, *rest]) = rest\n";

    private const string Payload = "Payload(('packet', *fields, 'end')) = fields\n";

    private static async Task<string> RunAsync(string source)
        => (await RepeatedNameConstraintTests.OnEveryRouteAsync(source)).Outcome;

    /// <summary><c>ok …</c> verbatim; an error reduced to its code (<c>err NoMatchingBranch</c>).</summary>
    private static string Category(string outcome)
        => outcome.StartsWith("ok ", StringComparison.Ordinal)
            ? outcome
            : outcome[..outcome.IndexOf(':', StringComparison.Ordinal)];

    // ── 1. The acceptance examples ───────────────────────────────────────────────────

    public static TheoryData<string, string> TailCalls => new()
    {
        // The headline example: nested values stay elements of the collected list.
        { "Tail(['a', ['b', 'c'], 'd'])", "ok L[L['b', 'c'], 'd']" },
        // The empty-list clause.
        { "Tail([])", "ok L[]" },
        // An empty collecting slice.
        { "Tail(['a'])", "ok L[]" },
        // Binding the unused head leaves that list position undemanded.
        { "Tail([1 / 0, 'b'])", "ok L['b']" },
        // One argument was supplied, and neither list pattern matches a sequence.
        { "Tail(('a', 'b'))", "err NoMatchingBranch" },
        // The family call's own cardinality, before branch selection.
        { "Tail('a', 'b')", "err ArityMismatch" },
        // A scalar and a string are one argument no list pattern matches.
        { "Tail(7)", "err NoMatchingBranch" },
        { "Tail('a')", "err NoMatchingBranch" },
        // A spread supplies its items as separate arguments: two, so the arity fails.
        { "Tail(['a', 'b']*)", "err ArityMismatch" },
    };

    [Theory]
    [MemberData(nameof(TailCalls))]
    public async Task ListPatternFamily_CollectsTheTail(string call, string expected)
        => Assert.Equal(expected, Category(await RunAsync(Tail + call)));

    [Fact]
    public async Task ArityMismatch_IsDecidedBeforeAnyBranchOrArgument()
    {
        // Neither argument is evaluated: the count is rejected before any clause is tried.
        var observation = await RepeatedNameConstraintTests.OnEveryRouteAsync(Tail + "Tail(trace(1), trace(2))");
        Assert.StartsWith("err ArityMismatch:", observation.Outcome, StringComparison.Ordinal);
        Assert.Empty(observation.HostCalls);

        // The payload is the family's fixed arity against the supplied count.
        var error = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(Tail + "Tail('a', 'b')"));
        var source = Assert.IsAssignableFrom<EvalError>(Assert.Single(error.Errors).Source);
        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(source));
        Assert.Equal((1, 2), (arity.Expected, arity.Actual));
    }

    public static TheoryData<string, string> PayloadCalls => new()
    {
        // A collector between fixed positions takes the exact middle.
        { "Payload(('packet', 10, [20, 30], 'end'))", "ok L[10, L[20, 30]]" },
        { "Payload(('packet', 'end'))", "ok L[]" },
        // The wrong closing literal.
        { "Payload(('packet', 10, 'stop'))", "err NoMatchingBranch" },
        // The wrong opening literal, too few elements, the other kind, a scalar.
        { "Payload(('parcel', 10, 'end'))", "err NoMatchingBranch" },
        { "Payload('packet')", "err NoMatchingBranch" },
        { "Payload(['packet', 'end'])", "err NoMatchingBranch" },
        // The sequence pattern consumes ONE argument however many elements `fields` takes.
        { "Payload('packet', 10, 'end')", "err ArityMismatch" },
        { "Payload(('packet', 10, 'end')*)", "err ArityMismatch" },
    };

    [Theory]
    [MemberData(nameof(PayloadCalls))]
    public async Task LiteralBearingClause_IsAFamilyThatCollectsBetweenFixedPositions(string call, string expected)
        => Assert.Equal(expected, Category(await RunAsync(Payload + call)));

    /// <summary>
    /// The evaluated examples of the Constitution's PAT-04 and VAR-02 as that document writes them
    /// (<c>docs/constitution/constitution.md</c>; no test reads the document, so these rows are its pins).
    /// </summary>
    public static TheoryData<string, string> ConstitutionExamples => new()
    {
        { Tail + "Tail(['a', ['b', 'c'], 'd']), Tail([]), Tail(['a']), Tail([1 / 0, 'b'])", "ok S[L[L['b', 'c'], 'd'], L[], L[], L['b']]" },
        { Payload + "Payload(('packet', 10, [20, 30], 'end')), Payload(('packet', 'end'))", "ok S[L[10, L[20, 30]], L[]]" },
        { "Rest(head, *rest) = rest\nRest(1, 2, 3)", "ok L[2, 3]" },
        { Tail + "Tail([1, 2, 3])", "ok L[2, 3]" },
        { "First([head, *rest]) = head\nFirst(xs) = 0\nK = First + 1\nK([7, 8])", "ok 8" },
    };

    [Theory]
    [MemberData(nameof(ConstitutionExamples))]
    public async Task ConstitutionExamples_HoldAsWritten(string source, string expected)
        => Assert.Equal(expected, await RunAsync(source));

    [Fact]
    public void Classification_IsOfTheWholeGroup()
    {
        // A single literal-bearing clause and a two-clause group are families; a single
        // literal-free clause is an ordinary algorithm, with its collectors where it wrote them.
        Assert.IsType<Algorithm.Conditional>(PropertyOf(Payload + "1", "Payload"));
        Assert.Equal(2, Assert.IsType<Algorithm.Conditional>(PropertyOf(Tail + "1", "Tail")).Branches.Count);

        var args = Assert.IsType<Algorithm.User>(PropertyOf("TailArgs(head, *rest) = rest\n1", "TailArgs"));
        Assert.Equal(["head", "*rest"], args.ParameterPatterns.Select(static pattern => pattern.DisplayName));
        var nested = Assert.IsType<Algorithm.User>(PropertyOf("OrdinaryTail([head, *rest]) = rest\n1", "OrdinaryTail"));
        Assert.Equal(["[head, *rest]"], nested.ParameterPatterns.Select(static pattern => pattern.DisplayName));
    }

    // ── 2. Adding a clause keeps the meaning of the nonempty-list pattern ────────────

    public static TheoryData<string> ListArguments => new()
    {
        "[1]", "[1, 2]", "[1, 2, 3]", "[(1, 2), [3], ()]", "[[], []]", "['a', true, 2.50]",
    };

    [Theory]
    [MemberData(nameof(ListArguments))]
    public async Task EmptyListClause_LeavesTheNonemptyPatternUnchanged(string argument)
    {
        var ordinary = await RunAsync($"OrdinaryTail([head, *rest]) = rest\nOrdinaryTail({argument})");
        var family = await RunAsync($"{Tail}Tail({argument})");
        Assert.StartsWith("ok L[", ordinary, StringComparison.Ordinal);
        Assert.Equal(ordinary, family);
    }

    [Fact]
    public async Task OnlyTheMismatchDiffers_BetweenTheOrdinaryDefinitionAndTheFamily()
    {
        Assert.Equal("err TypeMismatch", Category(await RunAsync("OrdinaryTail([head, *rest]) = rest\nOrdinaryTail((1, 2))")));
        Assert.Equal("err ArityMismatch", Category(await RunAsync("OrdinaryTail([head, *rest]) = rest\nOrdinaryTail([])")));
        Assert.Equal("err NoMatchingBranch", Category(await RunAsync(Tail + "Tail((1, 2))")));
        // A single collecting clause beside a literal clause: the empty list matches nothing.
        Assert.Equal("err NoMatchingBranch", Category(await RunAsync("T(0) = 0\nT([head, *rest]) = rest\nT([])")));
    }

    [Fact]
    public async Task OrdinaryEntryPoint_GathersSeparateArguments()
    {
        // The decision's recommended spelling for a caller that wants separate arguments.
        Assert.Equal("ok L[2, 3]", await RunAsync(Tail + "TailArgs(*items) = Tail(items)\nTailArgs(1, 2, 3)"));
        Assert.Equal("ok L[]", await RunAsync(Tail + "TailArgs(*items) = Tail(items)\nTailArgs()"));
        // Ordinary top-level collectors are unchanged.
        Assert.Equal("ok L[2, 3]", await RunAsync("Rest(head, *rest) = rest\nRest(1, 2, 3)"));
        Assert.Equal("ok S[L[1, 2], 3]", await RunAsync("Split(*prefix, last) = prefix, last\nSplit(1, 2, 3)"));
        Assert.Equal("ok L[]", await RunAsync("Only(*xs) = xs\nOnly"));
    }

    // ── 3. Nesting, fallback and failure ─────────────────────────────────────────────

    private const string Deep =
        "Deep(('pair', [x, (first, *others)])) = others\n" +
        "Deep((tag, [x, *more])) = more\n" +
        "Deep(other) = 'fallback'\n";

    public static TheoryData<string, string> DeepCalls => new()
    {
        // The collector two structural levels below the argument.
        { "Deep(('pair', [1, (2, 3, 4)]))", "ok L[3, 4]" },
        { "Deep(('pair', [1, (2, 3)]))", "ok L[3]" },
        // The first clause fails on its literal; the second matches the same supply and
        // collects the nested sequence whole, as one element.
        { "Deep(('other', [1, (2, 3)]))", "ok L[S[2, 3]]" },
        // The first clause fails on the inner list's cardinality, then on the inner kind.
        { "Deep(('pair', [1, 2, 3]))", "ok L[2, 3]" },
        { "Deep(('pair', [1, 2]))", "ok L[2]" },
        // Neither structural clause matches.
        { "Deep(7)", "ok 'fallback'" },
        { "Deep(('pair', 7))", "ok 'fallback'" },
        { "Deep(['pair', [1, 2]])", "ok 'fallback'" },
        // A list position only a plain binder takes is never demanded by matching.
        { "Deep(('none', [1 / 0, 9]))", "ok L[9]" },
        // The argument a structural pattern must open fails: dispatch aborts.
        { "Deep((1 / 0, [1, 2]))", "err DivisionByZero" },
    };

    [Theory]
    [MemberData(nameof(DeepCalls))]
    public async Task NestedCollector_FailedFirstClause_AndFallback(string call, string expected)
        => Assert.Equal(expected, Category(await RunAsync(Deep + call)));

    public static TheoryData<string, string> DemandCalls => new()
    {
        { "Lit([0, 2, 3])", "ok L[2, 3]" },
        { "Lit([1, 2])", "ok 'other'" },
        // The literal demands the first position: its failure propagates and the catch-all
        // is not tried.
        { "Lit([1 / 0, 2])", "err DivisionByZero" },
        // A collected position is demanded when the collected list is read whole: the
        // branch's result is one value, so returning `rest` reads every element.
        { "Lit([0, 1 / 0])", "err DivisionByZero" },
        // Inside the body the collector is the retained slice: counting it reads no element.
        { "Size([0, 1 / 0, 1 / 0])", "ok 2" },
        { "Size([1, 1 / 0])", "ok -1" },
    };

    [Theory]
    [MemberData(nameof(DemandCalls))]
    public async Task DemandedField_FailurePropagates_AndIsNeverANonMatch(string call, string expected)
        => Assert.Equal(expected, Category(await RunAsync(
            "Lit([0, *rest]) = rest\nLit(other) = 'other'\n" +
            "Size([0, *rest]) = rest.count\nSize(other) = -1\n" + call)));

    [Fact]
    public async Task Matching_DemandsOnlyWhatThePatternsInspect()
    {
        // Each clause attempt reads the SAME supplied cell: the argument is evaluated once,
        // although two clauses inspect it.
        var observation = await RepeatedNameConstraintTests.OnEveryRouteAsync(
            Tail + "Tail(trace([1, 2, 3]))");
        Assert.Equal("ok L[2, 3]", observation.Outcome);
        Assert.Single(observation.HostCalls);

        // A collected element is not demanded by matching, and an unread head never runs.
        var unread = await RepeatedNameConstraintTests.OnEveryRouteAsync(
            "Count([]) = 0\nCount([head, *rest]) = 1 + rest.count\nCount([trace(1), trace(2), trace(3)])");
        Assert.Equal("ok 3", unread.Outcome);
        Assert.Empty(unread.HostCalls);
    }

    [Fact]
    public async Task RecursiveListProcessing_ReadsNaturally()
    {
        const string source =
            "Len([]) = 0\n" +
            "Len([head, *rest]) = 1 + Len(rest)\n" +
            "Sum([]) = 0\n" +
            "Sum([head, *rest]) = head + Sum(rest)\n" +
            "Last([only]) = only\n" +
            "Last([head, *rest]) = Last(rest)\n" +
            "Len([4, 5, 6]), Sum([4, 5, 6]), Last([4, 5, 6])";
        Assert.Equal("ok S[3, 15, 6]", await RunAsync(source));
    }

    [Fact]
    public async Task Family_IsAnOrdinaryCallable()
    {
        // A callback element is one argument, exactly as at a direct call.
        Assert.Equal("ok L[L[2, 3], L[], L[]]", await RunAsync(Tail + "map([[1, 2, 3], [4], []], Tail)"));
        Assert.Equal("ok L[2, 3]", await RunAsync(Tail + "[1, 2, 3].Tail"));
        // The family's zero-argument value demand is unchanged (PAT-11).
        Assert.Equal("err NoMatchingBranch", Category(await RunAsync(Tail + "Tail")));
    }

    // ── 4. The family matrix: a collecting pattern selects exactly like the ordinary one ──

    public static TheoryData<string, string, string> FamilyBindings => new()
    {
        { "(*xs)", "()", "ok L[L[]]" },
        { "(*xs)", "(1, 2)", "ok L[L[1, 2]]" },
        { "(x, *rest)", "(1, 2)", "ok L[1, L[2]]" },
        { "(x, *rest)", "(1, 2, 3)", "ok L[1, L[2, 3]]" },
        { "(x, *middle, z)", "(1, 2)", "ok L[1, L[], 2]" },
        { "(x, *middle, z)", "(1, 2, 3, 4)", "ok L[1, L[2, 3], 4]" },
        { "[*xs]", "[]", "ok L[L[]]" },
        { "[*xs]", "[7]", "ok L[L[7]]" },
        { "[x, *rest]", "[7]", "ok L[7, L[]]" },
        { "[x, *rest]", "[(1, 2), [3]]", "ok L[S[1, 2], L[L[3]]]" },
        { "[x, *middle, z]", "[1, 2]", "ok L[1, L[], 2]" },
        { "[*prefix, z]", "[1, 2, 3]", "ok L[L[1, 2], 3]" },
        { "[*prefix, z]", "[7]", "ok L[L[], 7]" },
        // Mixed kinds, a collector at each level.
        { "[(x, *r), *s]", "[(1, 2, 3), 4, 5]", "ok L[1, L[2, 3], L[4, 5]]" },
        { "([*a], [*b])", "([], [1])", "ok L[L[], L[1]]" },
        // Non-matches reach the catch-all: wrong kind, too few elements.
        { "(x, *rest)", "[1, 2]", "ok 'miss'" },
        { "(x, *rest)", "7", "ok 'miss'" },
        { "(x, *rest)", "()", "ok 'miss'" },
        { "[x, *rest]", "(1, 2)", "ok 'miss'" },
        { "[x, *rest]", "[]", "ok 'miss'" },
        { "[x, *middle, z]", "[1]", "ok 'miss'" },
        { "(*xs)", "[1]", "ok 'miss'" },
        { "[*xs]", "(1, 2)", "ok 'miss'" },
        { "[(x, *r), *s]", "[[1, 2], 3]", "ok 'miss'" },
    };

    [Theory]
    [MemberData(nameof(FamilyBindings))]
    public async Task CollectingPattern_BindsInAFamilyExactlyAsInAnOrdinaryDefinition(string head, string value, string expected)
    {
        var names = head.Split([',', '(', ')', '[', ']', ' ', '*'], StringSplitOptions.RemoveEmptyEntries);
        var body = "[" + string.Join(", ", names) + "]";
        Assert.Equal(expected, await RunAsync($"F({head}) = {body}\nF(other) = 'miss'\nF({value})"));
        if (expected != "ok 'miss'")
            Assert.Equal(expected, await RunAsync($"P({head}) = {body}\nP({value})"));
    }

    // ── 5. Front-end rules ───────────────────────────────────────────────────────────

    public static TheoryData<string, int, int> DirectFamilyCollectors => new()
    {
        // (source, reported clause line, the exclusive end column of that whole clause)
        { "F(0, 0) = 0\nF(head, *rest) = rest\n1", 2, 22 },
        { "F(0) = 0\nF(*xs) = xs\n1", 2, 12 },
        { "F(*xs) = xs\nF(0) = 0\n1", 1, 12 },
        // A single literal-bearing clause is a family.
        { "F(0, *rest) = rest\n1", 1, 19 },
        { "F('tag', *rest) = rest\n1", 1, 23 },
        // A valid nested collector beside the direct one is still a direct collector.
        { "F(0, [x, *inner], *rest) = rest\n1", 1, 32 },
    };

    [Theory]
    [MemberData(nameof(DirectFamilyCollectors))]
    public void DirectFamilyCollector_IsInvalidCollectingBinding(string source, int line, int endColumn)
    {
        var diagnostic = Assert.Single(SourceProvenance.ExpectFrontEndError(source));
        Assert.Equal(DiagnosticCode.InvalidCollectingBinding, diagnostic.Code);
        Assert.Equal(Parser.FamilyDirectCollectorDiagnosticFor("F"), diagnostic.Message);
        Assert.Equal(new SourceSpan(line, 1, line, endColumn), diagnostic.Span);
        Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source));
    }

    [Fact]
    public void DirectFamilyCollectorWording_NamesTheRuleAndTheRepair()
    {
        Assert.Equal(
            "Clause family 'F' has one fixed call arity, so a collecting binding cannot stand directly among its call arguments. Collect inside a list pattern `[head, *rest]` or a sequence pattern `(head, *rest)`, or gather the arguments in an ordinary single-clause definition.",
            Parser.FamilyDirectCollectorDiagnosticFor("F"));
        Assert.Equal(
            "A clause family has one fixed call arity, so a collecting binding cannot stand directly among its call arguments. Collect inside a list pattern `[head, *rest]` or a sequence pattern `(head, *rest)`, or gather the arguments in an ordinary single-clause definition.",
            Parser.FamilyDirectCollectorDiagnostic);
    }

    public static TheoryData<string, DiagnosticCode, string> NestedCollectorRuleViolations => new()
    {
        // One collector per pattern level, in a family and in a literal-bearing clause.
        { "F([]) = 0\nF([*a, *b]) = 1\n1", DiagnosticCode.InvalidCollectingBinding, Parser.MultipleCollectingBindingsPerLevelDiagnostic },
        { "F((0, *a, x, *b)) = 1\n1", DiagnosticCode.InvalidCollectingBinding, Parser.MultipleCollectingBindingsPerLevelDiagnostic },
        { "F(0) = 0\nF([x, (*a, y, *b)]) = 1\n1", DiagnosticCode.InvalidCollectingBinding, Parser.MultipleCollectingBindingsPerLevelDiagnostic },
        // No repeated name involving a collector, within a level and across levels.
        { "F([]) = 0\nF([x, *x]) = 1\n1", DiagnosticCode.InvalidCollectingBinding, Parser.RepeatedNameIncludesCollectingDiagnostic },
        { "F((0, r, [*r])) = 1\n1", DiagnosticCode.InvalidCollectingBinding, Parser.RepeatedNameIncludesCollectingDiagnostic },
        { "F(0, 0) = 0\nF([*r], [*r]) = 1\n1", DiagnosticCode.InvalidCollectingBinding, Parser.RepeatedNameIncludesCollectingDiagnostic },
        // The singleton rule: a group around a collector-only sequence pattern is a one-item
        // sequence pattern, and so is one around a fixed name.
        { "F(0) = 0\nF(((*xs))) = 1\n1", DiagnosticCode.SingletonSequencePattern, Parser.SingletonSequencePatternDiagnostic },
        { "F(0) = 0\nF(([x, *rest])) = 1\n1", DiagnosticCode.SingletonSequencePattern, Parser.SingletonSequencePatternDiagnostic },
    };

    [Theory]
    [MemberData(nameof(NestedCollectorRuleViolations))]
    public void NestedCollector_IsHeldToTheOrdinaryStructuralRules(string source, DiagnosticCode code, string message)
    {
        var diagnostic = Assert.Single(SourceProvenance.ExpectFrontEndError(source));
        Assert.Equal(code, diagnostic.Code);
        Assert.Equal(message, diagnostic.Message);
    }

    public static TheoryData<string, string> ValidFamilies => new()
    {
        // One collector per level is satisfied by collectors at different levels.
        { "F(0) = 0\nF([*a, (x, *b)]) = [a, x, b]\nF([1, 2, (3, 4, 5)])", "ok L[L[1, 2], 3, L[4, 5]]" },
        // A repeated FIXED name stays a constraint beside a collector of another name (PAT-09).
        { "F([]) = 'empty'\nF([x, x, *rest]) = rest\nF(other) = 'other'\nF([1, 1, 2]), F([1, 2, 3])", "ok S[L[2], 'other']" },
        // The collector-only sequence pattern is valid and matches every sequence.
        { "F(0) = 'zero'\nF((*xs)) = xs\nF(()), F((1, 2)), F(0)", "ok S[L[], L[1, 2], 'zero']" },
        // Several arguments, each with its own collector.
        { "F(0, 0) = 0\nF([a, *as], (b, *bs)) = [a, as, b, bs]\nF([1, 2], (3, 4, 5))", "ok L[1, L[2], 3, L[4, 5]]" },
        // The same collector name in different clauses: a name belongs to its branch.
        { "F([]) = 0\nF([x, *rest]) = rest.count\nF((x, *rest)) = 10 + rest.count\nF([1, 2, 3]), F((1, 2, 3))", "ok S[2, 12]" },
    };

    [Theory]
    [MemberData(nameof(ValidFamilies))]
    public async Task ValidFamilyHeads_Evaluate(string source, string expected)
        => Assert.Equal(expected, await RunAsync(source));

    // ── 6. Duplicate heads ───────────────────────────────────────────────────────────

    [Theory]
    [InlineData("F([head, *rest]) = 1\nF([first, *others]) = 2\n1")]
    [InlineData("F((0, *xs)) = 1\nF((0, *ys)) = 2\n1")]
    [InlineData("F([x, (y, *r)]) = 1\nF(0) = 0\nF([a, (b, *c)]) = 2\n1")]
    [InlineData("F([*xs]) = 1\nF([*ys]) = 2\n1")]
    public void RenamedCollectingHeads_AreDuplicates(string source)
    {
        var diagnostic = Assert.Single(SourceProvenance.ExpectFrontEndError(source));
        Assert.Equal(DiagnosticCode.DuplicateBranchPattern, diagnostic.Code);
    }

    [Fact]
    public async Task FixedAndCollectingHeads_AreDistinct()
    {
        // `[x]` and `[*xs]` are different heads: written order decides the one-element list.
        Assert.Equal(
            "ok S['one', 'any', 'any']",
            await RunAsync("K([x]) = 'one'\nK([*xs]) = 'any'\nK([1]), K([]), K([1, 2])"));
        Assert.Equal(
            "ok S['any', 'any', 'any']",
            await RunAsync("K([*xs]) = 'any'\nK([x]) = 'one'\nK([1]), K([]), K([1, 2])"));
        // The collector's position and the structural kind distinguish heads too: three heads,
        // no duplicate, although the second can never be selected after the first.
        Assert.Equal(
            "ok S['first', 'seq']",
            await RunAsync("K([x, *r]) = 'first'\nK([*r, x]) = 'last'\nK((x, *r)) = 'seq'\nK([1]), K((1, 2))"));
    }

    [Fact]
    public void MatchEquivalence_AndItsIndex_AgreeOnCollectingHeads()
    {
        static Pattern Fixed(string name) => new Pattern.Bind(name);
        static Pattern Collecting(string name) => new Pattern.Bind(name) { ParameterKind = ParameterKind.Collecting };
        static Pattern List(params Pattern[] items) => new Pattern.ListValue(items);
        static Pattern Sequence(params Pattern[] items) => new Pattern.SequenceValue(items);

        (Pattern Left, Pattern Right, bool Equivalent)[] pairs =
        [
            (List(Fixed("head"), Collecting("rest")), List(Fixed("first"), Collecting("others")), true),
            (List(Fixed("x")), List(Collecting("xs")), false),
            (List(Collecting("xs")), List(Fixed("x")), false),
            (List(Fixed("x"), Collecting("r")), List(Collecting("r"), Fixed("x")), false),
            (List(Fixed("x"), Collecting("r")), Sequence(Fixed("x"), Collecting("r")), false),
            (Sequence(new Pattern.LitString("packet"), Collecting("fields"), new Pattern.LitString("end")),
                Sequence(new Pattern.LitString("packet"), Collecting("payload"), new Pattern.LitString("end")), true),
            (Sequence(Fixed("x"), List(Collecting("x2"))), Sequence(Fixed("a"), List(Collecting("b"))), true),
            (Collecting("xs"), Fixed("xs"), false),
        ];

        foreach (var (left, right, equivalent) in pairs)
        {
            Assert.Equal(equivalent, left.IsMatchEquivalent(right));
            Assert.Equal(equivalent, right.IsMatchEquivalent(left));
            var index = new PatternMatchEquivalenceIndex();
            Assert.True(index.TryAdd(left));
            Assert.Equal(!equivalent, index.TryAdd(right));
        }
    }

    // ── 7. Host-built trees ──────────────────────────────────────────────────────────

    private static Pattern.Bind Collector(string name) => new(name) { ParameterKind = ParameterKind.Collecting };

    private static Algorithm Body(Expr output) => new Algorithm.User(null, [], [], [], [output]);

    private static EvalResult<Result> RunFamily(IReadOnlyList<CondBranch> branches, params Expr[] arguments)
    {
        var family = new Property("F", new Algorithm.Conditional(null, [], branches));
        var root = new Algorithm.User(null, [], [], [family], [new Expr.Call(new Expr.Resolve("F"), arguments)]);
        return Evaluator.Run(new Expr.AlgorithmExpr(root));
    }

    public static TheoryData<string, string> RefusedHostHeads => new()
    {
        { "direct", Parser.FamilyDirectCollectorDiagnostic },
        { "lone", Parser.FamilyDirectCollectorDiagnostic },
        { "literal-direct", Parser.FamilyDirectCollectorDiagnostic },
        { "two-nested", Parser.MultipleCollectingBindingsPerLevelDiagnostic },
        { "two-direct", Parser.MultipleCollectingBindingsPerLevelDiagnostic },
        { "repeated-in-level", Parser.RepeatedNameIncludesCollectingDiagnostic },
        { "repeated-unnamed", Parser.RepeatedNameIncludesCollectingDiagnostic },
        { "repeated-unnamed-collector-first", Parser.RepeatedNameIncludesCollectingDiagnostic },
        { "repeated-across-levels", Parser.RepeatedNameIncludesCollectingDiagnostic },
        { "shared-group", Parser.RepeatedNameIncludesCollectingDiagnostic },
        { "singleton-around-collector", Parser.SingletonSequencePatternDiagnostic },
    };

    [Theory]
    [MemberData(nameof(RefusedHostHeads))]
    public void HostBuiltFamilyHead_IsRefusedBeforeEvaluation(string shape, string message)
    {
        var sharedGroup = new Pattern.ListValue([Collector("r")]);
        Pattern head = shape switch
        {
            "direct" => new Pattern.SequenceValue([new Pattern.Bind("head"), Collector("rest")]),
            "lone" => Collector("xs"),
            "literal-direct" => new Pattern.SequenceValue([new Pattern.LitInt(0), Collector("rest")]),
            "two-nested" => new Pattern.SequenceValue([new Pattern.ListValue([Collector("a"), new Pattern.Bind("x"), Collector("b")])]),
            "two-direct" => new Pattern.SequenceValue([Collector("a"), Collector("b")]),
            "repeated-in-level" => new Pattern.SequenceValue([new Pattern.ListValue([new Pattern.Bind("x"), Collector("x")])]),
            // A host can construct a binder with a null name. Repeating that name with a
            // collector reaches the same pre-evaluation error in either order.
            "repeated-unnamed" => new Pattern.ListValue([new Pattern.Bind(null!), Collector(null!)]),
            "repeated-unnamed-collector-first" => new Pattern.ListValue([Collector(null!), new Pattern.Bind(null!)]),
            "repeated-across-levels" => new Pattern.SequenceValue([new Pattern.Bind("r"), new Pattern.ListValue([Collector("r")])]),
            // ONE group object under two positions denotes a head that binds `*r` twice.
            "shared-group" => new Pattern.SequenceValue([sharedGroup, sharedGroup]),
            "singleton-around-collector" => new Pattern.SequenceValue(
                [new Pattern.SequenceValue([new Pattern.SequenceValue([Collector("xs")])])]),
            _ => throw new ArgumentOutOfRangeException(nameof(shape)),
        };

        // The failing argument is never evaluated: the tree is refused first. A second clause
        // makes the group a family whatever the head holds.
        var literalArity = head is Pattern.SequenceValue { Items.Count: var count } ? count : 1;
        Pattern literalHead = literalArity == 1
            ? new Pattern.LitInt(0)
            : new Pattern.SequenceValue(Enumerable.Repeat<Pattern>(new Pattern.LitInt(0), literalArity).ToArray());
        var result = RunFamily(
            [new CondBranch(literalHead, Body(new Expr.Num(0))), new CondBranch(head, Body(new Expr.Num(7)))],
            new Expr.Binary(BinaryOp.Div, new Expr.Num(1), new Expr.Num(0)));
        Assert.True(result.IsError);
        Assert.Equal(new EvalError.IllegalInEval(message), result.Error);
    }

    [Fact]
    public void HostBuiltFamilyHead_WithANestedCollector_Evaluates()
    {
        // Tail([]) = [] / Tail([head, *rest]) = rest, built by a host.
        CondBranch[] branches =
        [
            new(new Pattern.SequenceValue([new Pattern.ListValue([])]), Body(new Expr.ListLiteral([]))),
            new(new Pattern.SequenceValue([new Pattern.ListValue([new Pattern.Bind("head"), Collector("rest")])]),
                Body(new Expr.Param("rest"))),
        ];
        var list = new Expr.ListLiteral([new Expr.Num(1), new Expr.Num(2), new Expr.Num(3)]);
        var result = RunFamily(branches, list);
        if (result.IsError)
            Assert.Fail(result.Error.ToString());
        Assert.Equal("L[2, 3]", Neutral(result.Value));

        // A head that IS a list pattern (no argument-list wrapper) is one argument too.
        CondBranch[] bare =
        [
            new(new Pattern.ListValue([]), Body(new Expr.ListLiteral([]))),
            new(new Pattern.ListValue([new Pattern.Bind("head"), Collector("rest")]), Body(new Expr.Param("rest"))),
        ];
        var bareResult = RunFamily(bare, list);
        if (bareResult.IsError)
            Assert.Fail(bareResult.Error.ToString());
        Assert.Equal("L[2, 3]", Neutral(bareResult.Value));
        Assert.IsType<EvalError.ArityMismatch>(Innermost(RunFamily(bare, new Expr.Num(1), new Expr.Num(2)).Error));
    }

    [Fact]
    public void HeadRules_ReadAHostHeadThatSharesGroups_AsTheTreeItDenotes()
    {
        // A shared group WITHOUT a collector repeats only fixed names: no collector rule fires.
        var fixedGroup = new Pattern.ListValue([new Pattern.Bind("x")]);
        var sharedFixed = new Pattern.SequenceValue([fixedGroup, fixedGroup, new Pattern.ListValue([Collector("r")])]);
        Assert.False(sharedFixed.HasRepeatedNameIncludingCollecting());
        Assert.False(sharedFixed.HasMultipleCollectingLevel());
        Assert.False(sharedFixed.HeadHasDirectCollector());

        // A deep chain of shared groups is decided without expanding its paths.
        Pattern node = new Pattern.ListValue([Collector("deep")]);
        for (var depth = 0; depth < 64; depth++)
            node = new Pattern.SequenceValue([node, node]);
        Assert.True(node.HasRepeatedNameIncludingCollecting());
        Assert.False(node.HasMultipleCollectingLevel());
    }

    // ── 8. A nested collecting name belongs to its branch ────────────────────────────

    [Fact]
    public async Task NestedCollectingName_IsAParameterOfItsBranchOnly()
    {
        const string count = "Count(*items) = items.count\n";
        // An explicit call re-spreads the collector; passing it unspread passes one list.
        Assert.Equal(
            "ok S[2, 1]",
            await RunAsync(count + "F([]) = 0, 0\nF([head, *items]) = Count(items*), Count(items)\nF([1, 2, 3])"));

        // The name is bound in the clause that writes it and nowhere else: each clause's own
        // `rest` is its own binder, and a sibling clause without one does not see it.
        Assert.Equal(
            "ok S[L[2, 3], L[2]]",
            await RunAsync("F([first, *rest]) = rest\nF((first, *rest)) = rest\nF([1, 2, 3]), F((1, 2))"));
        var leaked = SourceProvenance.ExpectFrontEndError("F([]) = rest\nF([head, *rest]) = rest\n1");
        Assert.Contains(leaked, static diagnostic => diagnostic.Code == DiagnosticCode.UndeclaredIdentifier);

        // A block nested in the branch reads the collector as an enclosing parameter.
        Assert.Equal(
            "ok 5",
            await RunAsync("F([]) = 0\nF([head, *rest]) = {\n    Inner = rest.count + head\n    Inner\n}\nF([3, 8, 9])"));
    }

    [Fact]
    public async Task BareForwarding_SeesWholeOuterSlots_InABranchAsInAnOrdinaryBody()
    {
        // Bare forwarding hands a callee the body's same-named WHOLE argument positions. A
        // list-pattern position forwards as that pattern, in a branch exactly as in an
        // ordinary definition.
        const string target = "Target([head, *items]) = items.count\n";
        var ordinary = await RunAsync(target + "G([head, *items]) = Target\nG([1, 2, 3])");
        var family = await RunAsync(target + "F([]) = 0\nF([head, *items]) = Target\nF([1, 2, 3])");
        Assert.Equal("ok 2", ordinary);
        Assert.Equal(ordinary, family);

        // The nested collector alone is no outer slot: it never supplies a callee's own
        // top-level collecting parameter, in either kind of definition.
        const string count = "Count(*items) = items.count\n";
        var ordinaryRefusal = SourceProvenance.ExpectFrontEndError(count + "G([head, *items]) = Count\n1");
        var familyRefusal = SourceProvenance.ExpectFrontEndError(count + "F([]) = 0\nF([head, *items]) = Count\n1");
        Assert.Equal(
            ordinaryRefusal.Select(static diagnostic => diagnostic.Code),
            familyRefusal.Select(static diagnostic => diagnostic.Code));
        Assert.Contains(familyRefusal, static diagnostic => diagnostic.Code == DiagnosticCode.UnforwardableParameter);
    }

    [Fact]
    public async Task FamilyLifting_SeesWholeOuterSlots()
    {
        // The family's lifting signature names whole argument positions: a structural position
        // has no agreed plain name, so a formula that would lift the family is refused — the
        // nested collector's name is never offered as a parameter of the family.
        var unliftable = SourceProvenance.ExpectFrontEndError(Tail + "K = Tail + 1\n1");
        Assert.Contains(unliftable, static diagnostic => diagnostic.Code == DiagnosticCode.UnliftableClauseFamily);

        // A position that one clause destructures with a collecting list pattern and another
        // names plainly is ONE whole slot named by the plain clause: the lifted definition
        // takes `xs`, never `head` or `rest`, and dispatch is exactly the explicit call's.
        const string source = "First([head, *rest]) = head\nFirst(xs) = 0\nK = First + 1\n";
        var k = Assert.IsType<Algorithm.User>(PropertyOf(source + "K([7, 8])", "K"));
        Assert.Equal(["xs"], k.ParameterPatterns.Select(static pattern => pattern.DisplayName));
        Assert.Equal("ok S[8, 1, 1]", await RunAsync(source + "K([7, 8]), K(5), K([])"));
    }

    [Fact]
    public void Editor_BindsANestedCollectorOfABranch()
    {
        const string source = "Tail([]) = []\nTail([head, *rest]) = rest\nTail([1, 2])";
        var parsed = Parser.Parse(source);
        Assert.False(parsed.HasErrors, string.Join("\n", parsed.Diagnostics));
        var model = SemanticModelBuilder.Build(parsed);

        // The declaration is the written name `rest` of the second clause head; the collect
        // marker before it is punctuation and no identifier site.
        var rest = Assert.Single(model.FindDeclarations("rest"));
        Assert.Equal(OccurrenceKind.ConditionalBinderDefinition, rest.Kind);
        Assert.Equal(new SourceSpan(2, 14, 2, 18), rest.Span);

        // The body's `rest` resolves to that binder of its own branch.
        var reference = Assert.IsType<IdentifierResolution>(model.FindResolutionAt(new SourcePosition(2, 23)));
        Assert.Equal(new SourceSpan(2, 23, 2, 27), reference.Occurrence.Span);
        Assert.Equal(rest, reference.ResolvedDeclaration);

        // The binder keeps its collect marker for tooling, and the head renders as written.
        var head = Assert.IsType<Pattern.SequenceValue>(
            ((Algorithm.Conditional)parsed.Root.Properties.Single(static property => property.Name == "Tail").Value).Branches[1].Pattern);
        var list = Assert.IsType<Pattern.ListValue>(Assert.Single(head.Items));
        var binder = Assert.IsType<Pattern.Bind>(list.Items[1]);
        Assert.Equal(ParameterKind.Collecting, binder.ParameterKind);
        Assert.Equal(new SourceSpan(2, 13, 2, 14), binder.CollectMarkerSpan);
        Assert.Equal(
            ["Tail([])", "Tail([head, *rest])"],
            Assert.Single(model.FindProperties("Tail")).ConditionalBranches.Select(static branch => branch.HeadText));
    }

    // ── Support ──────────────────────────────────────────────────────────────────────

    private static Algorithm PropertyOf(string source, string name)
        => SourceProvenance.ParseValid(source).Root.Properties.Single(property => property.Name == name).Value;

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;
        return error;
    }

    private static string Neutral(Result value) => value switch
    {
        Result.Atom atom => Rendering.ValueTextRenderer.FormatNumberInvariant(atom.Value),
        Result.Str text => "'" + text.Value + "'",
        Result.Bool boolean => boolean.Value ? "true" : "false",
        Result.SequenceValue sequence => "S[" + string.Join(", ", sequence.Items.Select(Neutral)) + "]",
        Result.ListValue list => "L[" + string.Join(", ", list.Items.Select(Neutral)) + "]",
        _ => value.ToString() ?? "",
    };
}
