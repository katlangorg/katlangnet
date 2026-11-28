using System.Collections.Concurrent;

namespace KatLang.Tests;

/// <summary>
/// THE REACHABILITY WARNING AFTER A CATCH-ALL (Q-49, owner decision recorded 2026-11-28). In a written
/// clause family, each later, nonduplicate clause of the same arity after an unconditional catch-all
/// gets ONE non-blocking <see cref="DiagnosticCode.UnreachableClauseAfterCatchAll"/> warning over its
/// head, from the family name through the closing parenthesis, naming the catch-all by its head and
/// line. A catch-all has a plain binder in every top-level argument position, each name written once;
/// it is recognized from the written head alone. A repeated name, a literal, a list pattern and a
/// sequence pattern all inspect their arguments, so a head with one is no catch-all.
///
/// <para>The warning is advisory. Every branch, its order and its body are kept, dispatch still
/// selects the first match, and the program runs. A duplicate head reports
/// <see cref="DiagnosticCode.DuplicateBranchPattern"/> and gets no warning, an arity mismatch stays
/// <see cref="DiagnosticCode.BranchArityMismatch"/> (independent errors still apply: a duplicate of
/// the wrong arity reports both), and a head that needed recovery neither establishes a catch-all
/// nor is warned about.</para>
///
/// <para>Every expectation here is hand-written from the decision. Evaluated programs run on the six
/// execution routes of <see cref="RepeatedNameConstraintTests.OnEveryRouteAsync"/>, which must agree.
/// The warning is a C# front-end diagnostic with no Lean counterpart: Lean has no parser, and its
/// first-match dispatch (<c>evalConditional</c>) is unchanged.</para>
/// </summary>
public class UnreachableClauseAfterCatchAllTests
{
    private const DiagnosticCode Unreachable = DiagnosticCode.UnreachableClauseAfterCatchAll;

    /// <summary>The brief's acceptance program: the literal clause is written after the catch-all.</summary>
    private const string Shadowed = "Describe(x) = 'any'\nDescribe(0) = 'zero'\n";

    /// <summary>The same two declarations reversed: the literal clause is reachable.</summary>
    private const string Reversed = "Describe(0) = 'zero'\nDescribe(x) = 'any'\n";

    private static string Message(string catchAllHead, int line)
        => $"This clause is unreachable because the earlier '{catchAllHead}' clause on line {line} matches every argument.";

    private static async Task<string> RunAsync(string source)
        => (await RepeatedNameConstraintTests.OnEveryRouteAsync(source)).Outcome;

    private static IReadOnlyList<Diagnostic> Warnings(ParseResult parsed)
        => [.. parsed.Diagnostics.Where(static d => d.Code == Unreachable)];

    /// <summary>
    /// Asserts that the ONLY diagnostics of <paramref name="source"/> are reachability warnings, at exactly
    /// the given head spans, each identifying the given catch-all; returns the parse.
    /// </summary>
    private static ParseResult AssertWarnings(string source, string catchAllHead, int catchAllLine, params SourceSpan[] heads)
    {
        var parsed = Parser.Parse(source);
        Assert.False(parsed.HasErrors, string.Join("\n", parsed.Diagnostics));
        Assert.Equal(heads.Length, parsed.Diagnostics.Count);
        for (var index = 0; index < heads.Length; index++)
        {
            var warning = parsed.Diagnostics[index];
            Assert.Equal(DiagnosticSeverity.Warning, warning.Severity);
            Assert.Equal(Unreachable, warning.Code);
            Assert.Equal(heads[index], warning.Span);
            Assert.Equal(Message(catchAllHead, catchAllLine), warning.Message);
        }

        return parsed;
    }

    private static void AssertSilent(string source)
    {
        var parsed = Parser.Parse(source);
        Assert.True(parsed.Diagnostics.Count == 0, source + "\n" + string.Join("\n", parsed.Diagnostics));
    }

    // ── 1. The acceptance example ────────────────────────────────────────────────────

    [Fact]
    public void ClauseAfterACatchAll_GetsOneWarningOverItsHead()
    {
        var parsed = Parser.Parse(Shadowed + "Describe(0), Describe(1 / 0)");

        var warning = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticSeverity.Warning, warning.Severity);
        Assert.Equal(Unreachable, warning.Code);
        // `Describe(0)` on line 2: the family name through the closing parenthesis, nothing after it.
        Assert.Equal(new SourceSpan(2, 1, 2, 12), warning.Span);
        Assert.Equal(
            "This clause is unreachable because the earlier 'Describe(x)' clause on line 1 matches every argument.",
            warning.Message);

        // Parsing succeeds: a warning is not an error.
        Assert.False(parsed.HasErrors);
    }

    [Fact]
    public async Task ClauseAfterACatchAll_StillRuns_AndDispatchSelectsTheFirstMatch()
    {
        // Both calls return 'any': the catch-all is selected first and inspects no argument, so the
        // division is never evaluated.
        Assert.Equal("ok S['any', 'any']", await RunAsync(Shadowed + "Describe(0), Describe(1 / 0)"));

        // The warning never reaches a run result: the run is an ordinary success on both engine entries.
        var sync = Assert.IsType<RunResult.Success>(KatLangEngine.Run(Shadowed + "Describe(0)"));
        Assert.Equal(new Result.Str("any"), sync.Value);
        var asynchronous = Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(Shadowed + "Describe(0)"));
        Assert.Equal(new Result.Str("any"), asynchronous.Value);
    }

    [Fact]
    public async Task ReversedDeclarations_AreSilent_AndDemandTheirArgument()
    {
        AssertSilent(Reversed + "Describe(0), Describe(1 / 0)");

        // Exercised independently: the literal clause is tried first, so it demands the argument.
        Assert.Equal("ok 'zero'", await RunAsync(Reversed + "Describe(0)"));
        Assert.Equal("ok 'any'", await RunAsync(Reversed + "Describe(7)"));
        // This difference in argument demand is why reordering stays the author's decision: with the
        // literal first, matching it evaluates `1 / 0`, which the shadowed spelling never does.
        Assert.StartsWith("err DivisionByZero:", await RunAsync(Reversed + "Describe(1 / 0)"), StringComparison.Ordinal);
    }

    [Fact]
    public void WarnedFamily_KeepsEveryBranchItsOrderAndItsBody()
    {
        var parsed = Parser.Parse(Shadowed + "Describe(0)");

        var family = Assert.IsType<Algorithm.Conditional>(Assert.Single(parsed.Root.Properties).Value);
        Assert.Equal(2, family.Branches.Count);
        Assert.Equal("x", Assert.IsType<Pattern.Bind>(family.Branches[0].Pattern).Name);
        Assert.Equal(new Pattern.LitInt(0), family.Branches[1].Pattern);
        Assert.Equal("any", BodyText(family.Branches[0]));
        Assert.Equal("zero", BodyText(family.Branches[1]));

        // The reversed program has the same two branches in the other order: the warning changed neither.
        var reversedRoot = SourceProvenance.ParseValid(Reversed + "Describe(0)").Root;
        var reversed = Assert.IsType<Algorithm.Conditional>(Assert.Single(reversedRoot.Properties).Value);
        Assert.Equal(new Pattern.LitInt(0), reversed.Branches[0].Pattern);
        Assert.Equal("zero", BodyText(reversed.Branches[0]));
        Assert.Equal("x", Assert.IsType<Pattern.Bind>(reversed.Branches[1].Pattern).Name);
        Assert.Equal("any", BodyText(reversed.Branches[1]));

        static string BodyText(CondBranch branch)
            => Assert.IsType<Expr.StringLiteral>(Assert.Single(Assert.IsType<Algorithm.User>(branch.Body).Output)).Value;
    }

    /// <summary>
    /// The example of the Constitution's PAT-02 and the statements about its <c>Loose</c> family, as that
    /// document writes them (<c>docs/constitution/constitution.md</c>; no test reads the document, so these
    /// assertions are its pins).
    /// </summary>
    [Fact]
    public async Task ConstitutionExamples_HoldAsWritten()
    {
        const string example =
            "Describe(0) = 'zero'\nDescribe(n) = if(n > 0, 'positive', 'negative')\nLoose(n) = 'any'\nLoose(0) = 'zero'\n"
            + "Describe(0), Describe(-4), Describe(7), Loose(0)";

        // `Describe` has its catch-all last; `Loose` has it first.
        var warning = Assert.Single(Parser.Parse(example).Diagnostics);
        Assert.Equal(Unreachable, warning.Code);
        Assert.Equal(new SourceSpan(4, 1, 4, 9), warning.Span);
        Assert.Equal("This clause is unreachable because the earlier 'Loose(n)' clause on line 3 matches every argument.", warning.Message);
        Assert.Equal("ok S['zero', 'negative', 'positive', 'any']", await RunAsync(example));

        Assert.Equal("ok 'any'", await RunAsync("Loose(n) = 'any'\nLoose(0) = 'zero'\nLoose(1 / 0)"));
        AssertSilent("Loose(0) = 'zero'\nLoose(n) = 'any'\nLoose(0)");
        Assert.Equal("ok 'zero'", await RunAsync("Loose(0) = 'zero'\nLoose(n) = 'any'\nLoose(0)"));
        Assert.StartsWith("err DivisionByZero:", await RunAsync("Loose(0) = 'zero'\nLoose(n) = 'any'\nLoose(1 / 0)"), StringComparison.Ordinal);

        // General pattern coverage is not analysed: the second clause is selected by no call, and nothing is reported.
        AssertSilent("K([x, *r]) = 'first'\nK([*r, x]) = 'last'\nK([1, 2])");
        Assert.Equal("ok S['first', 'first']", await RunAsync("K([x, *r]) = 'first'\nK([*r, x]) = 'last'\nK([1, 2]), K([1])"));
    }

    // ── 2. Every later clause of the arity; each family has its own state ────────────

    [Fact]
    public void EveryLaterClauseOfTheArity_IsWarned()
    {
        AssertWarnings(
            "F(x, y) = 'any'\nF(0, 1) = 'a'\nF(1, 0) = 'b'\nF(0, 1)",
            "F(x, y)",
            1,
            new SourceSpan(2, 1, 2, 8),
            new SourceSpan(3, 1, 3, 8));
    }

    [Fact]
    public async Task InterleavedFamilies_KeepTheirOwnState()
    {
        // G's clauses stand between F's: G's catch-all is last, so only F's later clauses are warned.
        const string source = "F(x, y) = 'any'\nG(0) = 'g0'\nF(0, 1) = 'a'\nG(n) = 'gn'\nF(1, 0) = 'b'\n";
        AssertWarnings(source + "F(0, 1), G(0), G(5)", "F(x, y)", 1, new SourceSpan(3, 1, 3, 8), new SourceSpan(5, 1, 5, 8));
        Assert.Equal("ok S['any', 'g0', 'gn']", await RunAsync(source + "F(0, 1), G(0), G(5)"));
    }

    [Fact]
    public async Task IdenticallyNamedFamilyInANestedScope_HasItsOwnState()
    {
        // The outer F has a catch-all first; the inner F, a different declaration, has it last.
        const string outerShadowed = "F(x) = 'outer'\nInner = {\n    F(0) = 'zero'\n    F(n) = 'other'\n    F(0)\n}\nF(0) = 'never'\n";
        AssertWarnings(outerShadowed + "Inner, F(0)", "F(x)", 1, new SourceSpan(7, 1, 7, 5));
        Assert.Equal("ok S['zero', 'outer']", await RunAsync(outerShadowed + "Inner, F(0)"));

        // And the other way round: the inner family's catch-all says nothing about the outer one.
        const string innerShadowed = "F(0) = 'zero'\nInner = {\n    F(x) = 'inner'\n    F(0) = 'never'\n    F(0)\n}\nF(n) = 'other'\n";
        AssertWarnings(innerShadowed + "Inner, F(0)", "F(x)", 3, new SourceSpan(4, 5, 4, 9));
        Assert.Equal("ok S['inner', 'zero']", await RunAsync(innerShadowed + "Inner, F(0)"));
    }

    [Fact]
    public void CatchAllThatIsNotTheFirstClause_ShadowsOnlyTheClausesAfterIt()
        => AssertWarnings(
            "F(0) = 'zero'\nF(x) = 'any'\nF(1) = 'one'\nF(2) = 'two'\nF(1)",
            "F(x)",
            2,
            new SourceSpan(3, 1, 3, 5),
            new SourceSpan(4, 1, 4, 5));

    [Fact]
    public void SingleClause_AndCatchAllWrittenLast_AreSilent()
    {
        AssertSilent("F(x) = x + 1\nF(1)");
        AssertSilent("F(x, y) = x + y\nF(1, 2)");
        AssertSilent("F(0) = 'zero'\nF(1) = 'one'\nF(x) = 'any'\nF(5)");
    }

    // ── 3. What is no catch-all: a head that inspects its arguments ──────────────────

    public static TheoryData<string, string> ConstrainedHeads => new()
    {
        // A repeated name is a compatibility check over the two arguments.
        { "F(x, x) = 'same'\nF(a, b) = 'different'\nF(1, 1), F(1, 2)", "ok S['same', 'different']" },
        // A list pattern inspects its argument's kind and length: the fallback stays reachable.
        { "F([x]) = 'one-item list'\nF(v) = 'other'\nF([1]), F(7)", "ok S['one-item list', 'other']" },
        // So does a sequence pattern, nested ones included.
        { "F((a, b)) = 'pair'\nF(v) = 'other'\nF((1, 2)), F(7)", "ok S['pair', 'other']" },
        { "F((a, (b, c))) = 'nested'\nF(v) = 'other'\nF((1, (2, 3))), F((1, 2))", "ok S['nested', 'other']" },
        { "F(x, (a, [b])) = 'shaped'\nF(x, y) = 'other'\nF(0, (1, [2])), F(0, 1)", "ok S['shaped', 'other']" },
        // A literal in one position is a constraint, whatever the other positions bind.
        { "F(x, 0) = 'zero'\nF(a, b) = 'other'\nF(5, 0), F(5, 1)", "ok S['zero', 'other']" },
        { "F('on', y) = 'on'\nF(a, b) = 'other'\nF('on', 1), F('off', 1)", "ok S['on', 'other']" },
        { "F(true) = 'yes'\nF(v) = 'other'\nF(true), F(1)", "ok S['yes', 'other']" },
        // A collecting binder inside a list pattern still inspects the list kind (Q-47).
        { "F([*items]) = 'list'\nF(v) = 'other'\nF([1, 2]), F(7)", "ok S['list', 'other']" },
        // A repeated name among three positions.
        { "F(a, b, a) = 'ends agree'\nF(a, b, c) = 'other'\nF(1, 2, 1), F(1, 2, 3)", "ok S['ends agree', 'other']" },
    };

    [Theory]
    [MemberData(nameof(ConstrainedHeads))]
    public async Task HeadThatInspectsItsArguments_IsNoCatchAll_AndTheFallbackIsReachable(string source, string expected)
    {
        AssertSilent(source);
        Assert.Equal(expected, await RunAsync(source));
    }

    [Fact]
    public void StructuralPatternAfterACatchAll_IsWarned()
    {
        // The catch-all is recognized from its own head; what the later clause's pattern is does not matter.
        AssertWarnings("F(v) = 'any'\nF([x]) = 'list'\nF((a, (b, c))) = 'nested'\nF(1)", "F(v)", 1,
            new SourceSpan(2, 1, 2, 7), new SourceSpan(3, 1, 3, 15));
        AssertWarnings("F(a, b) = 'any'\nF(x, x) = 'same'\nF(1, 1)", "F(a, b)", 1, new SourceSpan(2, 1, 2, 8));
    }

    [Fact]
    public void WideHeads_AreJudgedByTheSameRule()
    {
        // Nine positions: past the pairwise name comparison.
        const string distinct = "F(a, b, c, d, e, f, g, h, i) = 'any'\n";
        const string repeated = "F(a, b, c, d, e, f, g, h, a) = 'ends agree'\n";
        const string literal = "F(0, 0, 0, 0, 0, 0, 0, 0, 0) = 'zeros'\n";
        const string call = "F(1, 2, 3, 4, 5, 6, 7, 8, 9)";

        AssertWarnings(distinct + literal + call, "F(a, b, c, d, e, f, g, h, i)", 1, new SourceSpan(2, 1, 2, 29));
        AssertSilent(repeated + literal + call);
        AssertSilent(repeated + "F(a, b, c, d, e, f, g, h, i) = 'any'\n" + call);
    }

    // ── 4. A duplicate head suppresses the reachability warning ─────────────────────

    [Fact]
    public void RenamedCatchAll_IsTheDuplicateErrorAlone()
    {
        var diagnostic = Assert.Single(Parser.Parse("F(x) = 1\nF(y) = 2\nF(0)").Diagnostics);
        Assert.Equal(DiagnosticSeverity.Error, diagnostic.Severity);
        Assert.Equal(DiagnosticCode.DuplicateBranchPattern, diagnostic.Code);

        var multi = Assert.Single(Parser.Parse("F(x, y) = 1\nF(b, a) = 2\nF(0, 1)").Diagnostics);
        Assert.Equal(DiagnosticCode.DuplicateBranchPattern, multi.Code);
    }

    [Fact]
    public void DuplicateAfterACatchAll_IsTheDuplicateErrorAlone_WhileTheFirstCopyIsWarned()
    {
        var parsed = Parser.Parse("F(x) = 1\nF(0) = 2\nF(0) = 3\nF(0)");

        Assert.Equal(2, parsed.Diagnostics.Count);
        // The first literal clause: reachable by no call.
        Assert.Equal(Unreachable, parsed.Diagnostics[0].Code);
        Assert.Equal(DiagnosticSeverity.Warning, parsed.Diagnostics[0].Severity);
        Assert.Equal(new SourceSpan(2, 1, 2, 5), parsed.Diagnostics[0].Span);
        // Its duplicate: the existing error, and no second warning although the catch-all precedes both.
        Assert.Equal(DiagnosticCode.DuplicateBranchPattern, parsed.Diagnostics[1].Code);
        Assert.Equal(DiagnosticSeverity.Error, parsed.Diagnostics[1].Severity);
        Assert.Equal(3, parsed.Diagnostics[1].Span!.Value.Start.Line);
        Assert.True(parsed.HasErrors);
    }

    [Fact]
    public void DuplicateOfAClauseBeforeTheCatchAll_IsTheDuplicateErrorAlone()
    {
        var diagnostic = Assert.Single(Parser.Parse("F(0) = 1\nF(x) = 2\nF(0) = 3\nF(0)").Diagnostics);
        Assert.Equal(DiagnosticCode.DuplicateBranchPattern, diagnostic.Code);
        Assert.Equal(3, diagnostic.Span!.Value.Start.Line);
    }

    // ── 5. Recovered heads, arity mismatches and refused binders ─────────────────────

    public static TheoryData<string, string, DiagnosticCode[]> RecoveredOrRefusedHeads => new()
    {
        // A recovered head would read as a catch-all (`F(x, y)`), but establishes none.
        { "recovered-separator", "F(x y) = 1\nF(0, 1) = 2\nF(0, 1)", [DiagnosticCode.UnseparatedSameLineItem] },
        { "recovered-grace", "F(x~) = 1\nF(0) = 2\nF(0)", [DiagnosticCode.InvalidGraceMarker] },
        { "recovered-lexical", "F(@) = 1\nF(0) = 2\nF(0)", [DiagnosticCode.UnexpectedCharacter] },
        { "recovered-singleton", "F((x)) = 1\nF(0) = 2\nF(0)", [DiagnosticCode.SingletonSequencePattern] },
        // A recovered head after a real catch-all gets no speculative warning (and is no duplicate).
        { "later-recovered-grace", "F(x) = 1\nF(y~) = 2\nF(0)", [DiagnosticCode.InvalidGraceMarker] },
        { "later-recovered-lexical", "F(x) = 1\nF(@) = 2\nF(0)", [DiagnosticCode.UnexpectedCharacter] },
        { "later-recovered-separator", "F(x, y) = 1\nF(0 1) = 2\nF(0, 1)", [DiagnosticCode.UnseparatedSameLineItem] },
        // An arity mismatch keeps its existing diagnostic, in both directions.
        { "arity-after-catch-all", "F(x) = 1\nF(0, 1) = 2\nF(0)", [DiagnosticCode.BranchArityMismatch] },
        { "duplicate-of-wrong-arity", "F(x) = 1\nF(0, 1) = 2\nF(0, 1) = 3\nF(0)",
            [DiagnosticCode.DuplicateBranchPattern, DiagnosticCode.BranchArityMismatch, DiagnosticCode.BranchArityMismatch] },
        { "arity-catch-all-is-the-mismatch", "F(0, 1) = 1\nF(x) = 2\nF(0) = 3\nF(0, 1)", [DiagnosticCode.BranchArityMismatch, DiagnosticCode.BranchArityMismatch] },
        // A collector directly among the call arguments and a META binder are no plain binders, and a
        // family refuses both there. (A NESTED collector is legal, Q-47: `F([*items])` above.)
        { "direct-collector", "F(*xs) = 1\nF(0) = 2\nF(0)", [DiagnosticCode.InvalidCollectingBinding] },
        { "meta-binder", "F(meta x) = 1\nF(0) = 2\nF(0)", [DiagnosticCode.InvalidMetaParameter] },
    };

    [Theory]
    [MemberData(nameof(RecoveredOrRefusedHeads))]
    public void RecoveredOrRefusedHead_NeitherEstablishesACatchAllNorIsWarned(string id, string source, DiagnosticCode[] expected)
    {
        var parsed = Parser.Parse(source);

        Assert.True(
            expected.SequenceEqual(parsed.Diagnostics.Select(static d => d.Code)),
            $"{id}: expected [{string.Join(", ", expected)}], got [{string.Join(", ", parsed.Diagnostics.Select(static d => d.Code))}]");
        Assert.All(parsed.Diagnostics, static d => Assert.Equal(DiagnosticSeverity.Error, d.Severity));
    }

    [Fact]
    public void CatchAllOfTheFamilysArity_IsJudgedBesideAnArityMismatch()
    {
        // `F(x)` is the arity mismatch; `F(a, b)` is the family's catch-all, and it shadows `F(1, 2)`.
        var parsed = Parser.Parse("F(0, 1) = 1\nF(x) = 2\nF(a, b) = 3\nF(1, 2) = 4\nF(0, 1)");

        Assert.Equal(2, parsed.Diagnostics.Count);
        var warning = Assert.Single(Warnings(parsed));
        Assert.Equal(new SourceSpan(4, 1, 4, 8), warning.Span);
        Assert.Equal(Message("F(a, b)", 3), warning.Message);
        var mismatch = Assert.Single(parsed.Diagnostics, static d => d.Code == DiagnosticCode.BranchArityMismatch);
        Assert.Equal(2, mismatch.Span!.Value.Start.Line);
    }

    [Fact]
    public void WarningInsideANestedFamily_LeavesTheEnclosingClauseWellFormed()
    {
        // The first `Outer(0)` clause holds a nested family with a shadowed clause. The enclosing clause
        // is still a cleanly parsed head: it takes part in duplicate detection, so its copy is reported.
        var parsed = Parser.Parse(
            "Outer(0) = {\n    G(x) = 1\n    G(0) = 2\n    G(5)\n}\nOuter(0) = 9\nOuter(0)");

        Assert.Equal(2, parsed.Diagnostics.Count);
        Assert.Equal(Unreachable, parsed.Diagnostics[0].Code);
        Assert.Equal(new SourceSpan(3, 5, 3, 9), parsed.Diagnostics[0].Span);
        Assert.Equal(DiagnosticCode.DuplicateBranchPattern, parsed.Diagnostics[1].Code);

        // And it is the reference clause of the cross-clause arity check.
        var arity = Parser.Parse("Outer(0) = {\n    G(x) = 1\n    G(0) = 2\n    G(5)\n}\nOuter(a, b) = 9\nOuter(0)");
        Assert.Equal([Unreachable, DiagnosticCode.BranchArityMismatch], arity.Diagnostics.Select(static d => d.Code));

        // A nested family inside a catch-all's body, and inside a warned clause's body, are families of their
        // own. The warned clause's body is parsed before the clause is recorded, so its warning comes first.
        var nested = Parser.Parse(
            "Outer(n) = {\n    G(0) = 1\n    G(x) = 2\n    G(n)\n}\nOuter(0) = {\n    H(x) = 1\n    H(0) = 2\n    H(0)\n}\nOuter(0)");
        Assert.False(nested.HasErrors, string.Join("\n", nested.Diagnostics));
        Assert.Equal(2, nested.Diagnostics.Count);
        Assert.Equal(new SourceSpan(8, 5, 8, 9), nested.Diagnostics[0].Span);
        Assert.Equal(Message("H(x)", 7), nested.Diagnostics[0].Message);
        Assert.Equal(new SourceSpan(6, 1, 6, 9), nested.Diagnostics[1].Span);
        Assert.Equal(Message("Outer(n)", 1), nested.Diagnostics[1].Message);
    }

    // ── 6. The head span and the identification of the earlier clause ────────────────

    [Fact]
    public void HeadSpan_RunsFromTheFamilyNameThroughTheClosingParenthesis()
    {
        // `public` is not part of the head.
        AssertWarnings("public F(x) = 1\npublic F(0) = 2\nF(0)", "F(x)", 1, new SourceSpan(2, 8, 2, 12));
        // Neither is the output-spreading marker after the closing parenthesis.
        AssertWarnings("F(x)* = x, x\nF(0)* = 0, 0\nF(0)", "F(x)", 1, new SourceSpan(2, 1, 2, 5));
        // A head written over two lines is underlined across them.
        AssertWarnings("F(x, y) = 1\nF(0,\n  1) = 2\nF(0, 1)", "F(x, y)", 1, new SourceSpan(2, 1, 3, 5));
        // An indented clause.
        AssertWarnings("A = {\n    F(first, second) = 1\n    F(  0 , 1  ) = 2\n    F(0, 1)\n}\nA", "F(first, second)", 2, new SourceSpan(3, 5, 3, 17));
    }

    [Fact]
    public void LongNames_AreBoundedInTheMessage()
    {
        var name = "F" + new string('a', 600);
        var binder = "x" + new string('b', 600);
        var parsed = Parser.Parse($"{name}({binder}) = 1\n{name}(0) = 2\n{name}(0)");

        var warning = Assert.Single(parsed.Diagnostics);
        Assert.Equal(Unreachable, warning.Code);
        // Each echoed name keeps its bounded prefix and the truncation marker, never the whole identifier.
        Assert.Contains($"'{name[..512]}…({binder[..512]}…)'", warning.Message, StringComparison.Ordinal);
        Assert.EndsWith(" clause on line 1 matches every argument.", warning.Message, StringComparison.Ordinal);
        Assert.True(warning.Message.Length < 1200, warning.Message.Length.ToString(System.Globalization.CultureInfo.InvariantCulture));
    }

    [Fact]
    public void Warning_ProjectsOntoTheErrorFacadeWithItsOwnCode()
    {
        var warning = Assert.Single(Parser.Parse(Shadowed + "Describe(0)").Diagnostics);
        var projected = KatLangError.FromDiagnostic(warning);

        Assert.Equal(KatLangErrorCode.UnreachableClauseAfterCatchAll, projected.Code);
        Assert.Equal(warning.Message, projected.Message);
        Assert.Equal(warning.Span, projected.Span);
        Assert.Equal("[2:1] " + warning.Message, projected.ToString());
    }

    // ── 7. The bounded diagnostic list ───────────────────────────────────────────────

    private static RunOptions Limited(int maxDiagnosticCount)
        => new() { SourceProcessingLimits = new SourceProcessingLimits { MaxDiagnosticCount = maxDiagnosticCount } };

    [Theory]
    [InlineData(1)]
    [InlineData(2)]
    public async Task WarningOnlySource_StillRunsAtASmallDiagnosticLimit(int limit)
    {
        // Three warnings, more than the list keeps.
        const string source = "F(x) = 'any'\nF(0) = 'a'\nF(1) = 'b'\nF(2) = 'c'\nF(0)";
        var parsed = Parser.Parse(source, Limited(limit));

        Assert.Equal(limit + 1, parsed.Diagnostics.Count);
        for (var index = 0; index < limit; index++)
        {
            Assert.Equal(Unreachable, parsed.Diagnostics[index].Code);
            Assert.Equal(new SourceSpan(index + 2, 1, index + 2, 5), parsed.Diagnostics[index].Span);
        }

        // The marker takes the severity of what it stands for: only warnings were omitted.
        var marker = parsed.Diagnostics[^1];
        Assert.Equal(DiagnosticCode.DiagnosticCountExceeded, marker.Code);
        Assert.Equal(DiagnosticSeverity.Warning, marker.Severity);
        Assert.Null(marker.Span);
        Assert.False(parsed.HasErrors);

        Assert.Equal(new Result.Str("any"), Assert.IsType<RunResult.Success>(KatLangEngine.Run(source, Limited(limit))).Value);
        Assert.Equal(new Result.Str("any"), Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(source, Limited(limit))).Value);
    }

    [Theory]
    [InlineData(1)]
    [InlineData(2)]
    public async Task LaterGenuineError_StillBlocksAtASmallDiagnosticLimit(int limit)
    {
        // Two warnings, then a real error the list has no room for.
        const string source = "F(x) = 'any'\nF(0) = 'a'\nF(1) = 'b'\nA = 1\nA = 2\nF(0)";
        var parsed = Parser.Parse(source, Limited(limit));

        Assert.Equal(limit + 1, parsed.Diagnostics.Count);
        Assert.All(parsed.Diagnostics.Take(limit), static d => Assert.Equal(DiagnosticSeverity.Warning, d.Severity));
        var marker = parsed.Diagnostics[^1];
        Assert.Equal(DiagnosticCode.DiagnosticCountExceeded, marker.Code);
        Assert.Equal(DiagnosticSeverity.Error, marker.Severity);
        Assert.True(parsed.HasErrors);

        // The engine refuses to evaluate, and reports the errors only: here the marker.
        var sync = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source, Limited(limit)));
        Assert.Equal(KatLangErrorCode.DiagnosticCountExceeded, Assert.Single(sync.Errors).Code);
        var asynchronous = Assert.IsType<RunResult.ParseFailure>(await KatLangEngine.RunAsync(source, Limited(limit)));
        Assert.Equal(KatLangErrorCode.DiagnosticCountExceeded, Assert.Single(asynchronous.Errors).Code);
    }

    [Fact]
    public void ErrorBesideWarnings_BlocksTheRun_AndTheRunReportsTheErrorOnly()
    {
        const string source = "F(x) = 'any'\nF(0) = 'a'\nF(1) = 'b'\nA = 1\nA = 2\nF(0)";
        var parsed = Parser.Parse(source);

        Assert.Equal([Unreachable, Unreachable, DiagnosticCode.DuplicateProperty], parsed.Diagnostics.Select(static d => d.Code));
        Assert.True(parsed.HasErrors);

        var failure = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source));
        Assert.Equal(KatLangErrorCode.DuplicateProperty, Assert.Single(failure.Errors).Code);
    }

    [Fact]
    public void RetainedErrorAndOmittedWarning_RunReportsOnlyTheError()
    {
        const string source = "A = 1\nA = 2\nF(x) = 1\nF(0) = 2\nF(0)";
        var parsed = Parser.Parse(source, Limited(1));
        Assert.Equal([DiagnosticCode.DuplicateProperty, DiagnosticCode.DiagnosticCountExceeded],
            parsed.Diagnostics.Select(static d => d.Code));
        Assert.Equal(DiagnosticSeverity.Warning, parsed.Diagnostics[1].Severity);
        var failure = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source, Limited(1)));
        Assert.Equal(KatLangErrorCode.DuplicateProperty, Assert.Single(failure.Errors).Code);
    }

    [Fact]
    public void WarningBag_CountsAReportButNeverAnError_AndFormatsOnlyWhatItStores()
    {
        var bag = new DiagnosticBag(capacity: 1);
        var formatted = 0;
        for (var index = 0; index < 3; index++)
        {
            bag.ReportWarning(Unreachable, null, index, state =>
            {
                formatted++;
                return $"w{state}";
            });
        }

        Assert.Equal(3, bag.ReportedCount);
        Assert.Equal(0, bag.ReportedErrorCount);
        Assert.False(bag.HasReportedErrors);
        Assert.True(bag.HasReported(Unreachable));
        // Only the stored report was formatted.
        Assert.Equal(1, formatted);
        Assert.Equal(["w0", "Diagnostic limit of 1 diagnostic reached: later diagnostics were omitted."], bag.Select(static d => d.Message));
        Assert.All(bag, static d => Assert.Equal(DiagnosticSeverity.Warning, d.Severity));

        // A later error raises the marker, and only then does the list block.
        bag.Report(DiagnosticCode.DuplicateProperty, "e", null);
        Assert.Equal(DiagnosticSeverity.Error, bag[^1].Severity);
        Assert.Equal(1, bag.ReportedErrorCount);
    }

    // ── 8. A loaded module's warning stays in the loading document's coordinates ─────

    private const string ModuleUrl = "https://katlang.org/q49/describe.kat";

    private sealed class Modules(string source)
    {
        public ConcurrentQueue<string> Requests { get; } = new();

        public ValueTask<string> Download(string url, CancellationToken cancellationToken)
        {
            Requests.Enqueue(url);
            return ValueTask.FromResult(source);
        }
    }

    [Fact]
    public async Task LoadedModuleWithAShadowedClause_WarnsAtTheLoadSite_AndTheProgramRuns()
    {
        // The module's second line holds the catch-all and its third holds the shadowed clause.
        var modules = new Modules("# a library\npublic Describe(x) = 'any'\npublic Describe(0) = 'zero'\n");
        var options = new RunOptions { DownloadCode = modules.Download };
        var source = $"Lib = load('{ModuleUrl}')\nOther = load('{ModuleUrl}')\nLib.Describe(0), Other.Describe(1 / 0)";

        var parsed = await Parser.ParseAsync(source, options);

        // One warning for the module, however many times the program loads it, at the first load site.
        var warning = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticSeverity.Warning, warning.Severity);
        Assert.Equal(Unreachable, warning.Code);
        Assert.Equal($"[while loading {ModuleUrl}] " + Message("Describe(x)", 2), warning.Message);
        Assert.Equal(new SourceSpan(1, 7, 1, 7 + $"load('{ModuleUrl}')".Length), warning.Span);
        Assert.False(parsed.HasErrors);
        // The parse downloaded the module once: the second load is the same declaration (Q-32).
        Assert.Single(modules.Requests);

        var run = Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(source, options));
        var rows = Assert.IsType<Result.SequenceValue>(run.Value);
        Assert.Equal([new Result.Str("any"), new Result.Str("any")], rows.Items);
    }

    [Fact]
    public async Task LongModuleUrl_LeavesTheCatchAllIdentifiableAtTheLoadSite()
    {
        var url = ModuleUrl + "?" + new string('a', 5000);
        var modules = new Modules("public F(x) = 1\npublic F(0) = 2");
        var load = $"load('{url}')";
        var parsed = await Parser.ParseAsync($"A = {load}\nA.F(0)", new RunOptions { DownloadCode = modules.Download });

        var warning = Assert.Single(parsed.Diagnostics);
        Assert.Equal(Unreachable, warning.Code);
        Assert.Equal(DiagnosticSeverity.Warning, warning.Severity);
        Assert.Equal(new SourceSpan(1, 5, 1, 5 + load.Length), warning.Span);
        Assert.Equal($"[while loading {url[..ModuleLoadTarget.MaxEchoedTargetLength]}...] " + Message("F(x)", 1), warning.Message);
        Assert.Equal(url, Assert.Single(modules.Requests));
    }

    [Fact]
    public async Task ModuleLoadedOnlyByASelectedBranch_RunsAndReportsNothing()
    {
        // A branch that loads its module on demand is compiled when it is selected (MOD-10): the parse never sees
        // the module, and a selection that succeeds has no diagnostic list to carry an advisory.
        var modules = new Modules("public Describe(x) = 'any'\npublic Describe(0) = 'zero'\n");
        var options = new RunOptions { DownloadCode = modules.Download };
        var source = $"Pick(0) = 'none'\nPick(k) = {{\n    Lib = load('{ModuleUrl}')\n    Lib.Describe(0)\n}}\nPick(1)";

        var parsed = await Parser.ParseAsync(source, options);
        Assert.Empty(parsed.Diagnostics);
        Assert.Empty(modules.Requests);

        var run = Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(source, options));
        Assert.Equal(new Result.Str("any"), run.Value);
        Assert.Single(modules.Requests);
    }
}
