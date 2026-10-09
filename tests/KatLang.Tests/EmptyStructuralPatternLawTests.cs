namespace KatLang.Tests;

/// <summary>
/// PAT-05 (corrected 2026-10-09; the structural-pattern model of PAT-06 is unchanged): PATTERNS USE THE PATTERN
/// GRAMMAR, NOT GENERAL EXPRESSION SYNTAX, AND <c>()</c> AND <c>[]</c> ARE VALID, DISTINCT STRUCTURAL PATTERNS.
/// An arithmetic expression such as <c>1 + 1</c>, a call, or any other non-pattern expression in a pattern
/// position is a front-end error; the empty sequence pattern <c>()</c> matches only the empty sequence and the
/// empty list pattern <c>[]</c> only the empty list, in clause families (a mismatch tries the next clause) and
/// in ordinary single-clause definitions (a mismatch fails the binding) alike. The former PAT-05 text — "<c>F(())</c>
/// and <c>F([])</c> are parse errors", "empty and list patterns do not exist" — predates the 2026-09-29
/// structural-pattern decision and is superseded.
/// <para>Every expectation is written from the law; every source runs on the six routes, which must agree with
/// the synchronous engine on value, every error (code, message, span) and the host-call log. Lean:
/// <c>CoreTests/EmptyStructuralPatterns.lean</c> (Lean's <c>Pattern</c> has no expression constructor, so the
/// parser diagnostics below are C#-only); spec cases <c>empty-structural-patterns-are-distinct-heads</c> and
/// <c>expression-is-not-a-pattern</c>.</para>
/// </summary>
public sealed class EmptyStructuralPatternLawTests
{
    private const string Singleton =
        "SingletonSequencePattern: A sequence pattern with exactly one non-collecting item is invalid: KatLang has no one-item sequence value. "
        + "Bind the whole value with a plain name, or use the list pattern `[x]` for a one-element list.";

    // ── 1. The canonical witnesses ─────────────────────────────────────────────────────────────────

    public static TheoryData<string, string, string> CanonicalWitnesses() => new()
    {
        // P1: the empty sequence pattern.
        { "P1", "F(()) = 1\nF(x) = 2\nF(()), F(5)", "S[1, 2]" },
        // P2: the empty list pattern.
        { "P2", "F([]) = 1\nF(x) = 2\nF([]), F(5)", "S[1, 2]" },
        // P3: both empty heads in one family: distinct structural kinds.
        {
            "P3", "Kind(()) = 'empty sequence'\nKind([]) = 'empty list'\nKind(x) = 'other'\nKind(()), Kind([]), Kind(0)",
            "S['empty sequence', 'empty list', 'other']"
        },
    };

    [Theory]
    [MemberData(nameof(CanonicalWitnesses))]
    public async Task CanonicalWitness_IsValidSourceWithTheAdoptedMeaning(string id, string source, string expected)
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.True(observation.Kind == "ok" && observation.Value == expected, $"{id}: expected ok {expected}, got {observation}");
    }

    // ── 2. The two empty kinds never match each other; value, not spelling, selects ─────────────────

    public static TheoryData<string, string, string> DistinctKinds() => new()
    {
        { "an empty list never matches ()", "F(()) = 1\nF(x) = 2\nF([])", "ok 2" },
        { "the PAT-05 rule's example", "F(()) = 1\nF(x) = 2\nF(()), F([])", "ok S[1, 2]" },
        { "an empty sequence never matches []", "G([]) = 1\nG(x) = 2\nG(())", "ok 2" },
        { "two different heads, not duplicates", "H(()) = 1\nH([]) = 2\nH(()), H([])", "ok S[1, 2]" },
        { "no catch-all: anything else is the family's NoMatchingBranch", "H(()) = 1\nH([]) = 2\nH(0)", "err NoMatchingBranch: while evaluating call to H: No matching branch for 'H' @ [3:1, 3:5)" },
        { "a property holding (), a redundant group and a computed list", "F(()) = 1\nF(x) = 2\nA = ()\nF(A), F((())), F(take((1, 2), 0))", "ok S[1, 1, 2]" },
        { "computed empty lists", "F([]) = 1\nF(x) = 2\nF(take((1, 2), 0)), F(([])), F(filter([1], { x > 5 }))", "ok S[1, 1, 1]" },
        { "an empty pattern beside a binder", "G((), y) = y\nG((), 5)", "ok 5" },
        { "an empty list pattern beside a binder", "G([], y) = y\nG([], 5)", "ok 5" },
        { "callback elements dispatch through the same heads", "F([]) = 0\nF([x]) = 1\nF(xs) = 2\nmap([[], [5], (), 7], F)", "ok L[0, 1, 2, 2]" },
    };

    [Theory]
    [MemberData(nameof(DistinctKinds))]
    public async Task EmptySequenceAndEmptyListPatterns_AreDistinctKinds(string label, string source, string expected)
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.True(expected == Outcome(observation), $"{label}: expected {expected}, got {observation}");
    }

    // ── 3. A single clause is an ordinary algorithm: wrong kind or length fails the binding ─────────

    public static TheoryData<string, string, string> OrdinaryDefinitions() => new()
    {
        { "E(()) given ()", "E(()) = 1\nE(())", "ok 1" },
        {
            "E(()) given []", "E(()) = 1\nE([])",
            "err TypeMismatch: while evaluating call to E: Type mismatch: sequence pattern `()` expects a sequence value, but received a list value with 0 elements: [] @ [2:1, 2:6)"
        },
        { "E(()) given a pair", "E(()) = 1\nE((1, 2))", "err ArityMismatch: Sequence pattern `()` expects 0 elements, but received 2 elements. @ [2:1, 2:10)" },
        {
            "E(()) given a number", "E(()) = 1\nE(5)",
            "err TypeMismatch: while evaluating call to E: Type mismatch: sequence pattern `()` expects a sequence value, but received numeric value 5 @ [2:1, 2:5)"
        },
        { "L([]) given []", "L([]) = 1\nL([])", "ok 1" },
        {
            "L([]) given ()", "L([]) = 1\nL(())",
            "err TypeMismatch: while evaluating call to L: Type mismatch: list pattern `[]` expects a list value, but received a sequence value with 0 sequence elements: () @ [2:1, 2:6)"
        },
        { "L([]) given a one-element list", "L([]) = 1\nL([7])", "err ArityMismatch: List pattern `[]` expects 0 elements, but received 1 element. @ [2:1, 2:7)" },
    };

    [Theory]
    [MemberData(nameof(OrdinaryDefinitions))]
    public async Task OrdinaryEmptyPatterns_FailTheBindingWithTheExistingCategories(string label, string source, string expected)
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.True(expected == Outcome(observation), $"{label}: expected {expected}, got {observation}");
    }

    // ── 4. Nested empties, collectors and lists keep their kind at every level ──────────────────────

    public static TheoryData<string, string, string> NestedStructures() => new()
    {
        { "a list whose element is []", "F([[]]) = 1\nF(x) = 2\nF([[]]), F([]), F([()])", "ok S[1, 2, 2]" },
        { "a list whose element is ()", "F([()]) = 1\nF(x) = 2\nF([()]), F([[]]), F(())", "ok S[1, 2, 2]" },
        { "a pair of both empties, in order", "F(((), [])) = 1\nF(x) = 2\nF(((), [])), F(([], ())), F(((), ()))", "ok S[1, 2, 2]" },
        { "the inner empty pattern selects the clause", "K(([], x)) = 'list-first'\nK(((), x)) = 'seq-first'\nK(y) = 'other'\nK(([], 1)), K(((), 1)), K((1, 1))", "ok S['list-first', 'seq-first', 'other']" },
        {
            "the inner kind fails an ordinary binding", "N(([], x)) = x\nN(((), 5))",
            "err TypeMismatch: while evaluating call to N: Type mismatch: list pattern `[]` expects a list value, but received a sequence value with 0 sequence elements: () @ [2:1, 2:11)"
        },
        { "a collector-only sequence pattern covers ()", "F((*xs)) = xs\nF(()), F((1, 2))", "ok S[L[], L[1, 2]]" },
        { "a collector-only list pattern covers []", "F([*xs]) = xs\nF([]), F([1, 2])", "ok S[L[], L[1, 2]]" },
        {
            "a collector-only sequence pattern never opens a list", "F((*xs)) = xs\nF([])",
            "err TypeMismatch: while evaluating call to F: Type mismatch: sequence pattern `(*xs)` expects a sequence value, but received a list value with 0 elements: [] @ [2:1, 2:6)"
        },
        { "a nonempty list pattern", "F([x, y]) = x + y\nF([1, 2])", "ok 3" },
        { "a negative number literal is a literal pattern", "F(-1) = 1\nF(x) = 0\nF(0 - 1), F(1)", "ok S[1, 0]" },
    };

    [Theory]
    [MemberData(nameof(NestedStructures))]
    public async Task NestedEmptyPatterns_KeepTheirKind(string label, string source, string expected)
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.True(expected == Outcome(observation), $"{label}: expected {expected}, got {observation}");
    }

    // ── 5. General expressions are not patterns ───────────────────────────────────────────────────

    public static TheoryData<string, string, string> ExpressionsAreNotPatterns() => new()
    {
        // P4: the canonical witness.
        { "arithmetic", "F(1 + 1) = 2\nF(2)", "UnexpectedToken: Expected ')' but found '+'. @ [1:5, 1:6)" },
        { "arithmetic over a binder", "F(x + 1) = x\nF(2)", "UnexpectedToken: Expected ')' but found '+'. @ [1:5, 1:6)" },
        { "arithmetic after a binder", "F(a, b + 1) = a\nF(1, 2)", "UnexpectedToken: Expected ')' but found '+'. @ [1:8, 1:9)" },
        { "arithmetic inside a list pattern", "F([1 + 1]) = 1\nF([2])", "UnexpectedToken: Expected ']' but found '+'. @ [1:6, 1:7)" },
        // A call shape is a binder followed by an unseparated pattern `(1)`, which is also a singleton.
        { "a call", "F(f(1)) = 1\nF(2)", "UnseparatedSameLineItem: Unexpected item after a parameter pattern on the same line. Add ',' to separate the patterns of a parameter list. @ [1:4, 1:5) | " + Singleton + " @ [1:4, 1:7)" },
    };

    [Theory]
    [MemberData(nameof(ExpressionsAreNotPatterns))]
    public async Task AnExpressionInAPatternPosition_IsAFrontEndError(string label, string source, string expectedErrors)
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.True(observation.Kind == "parse", $"{label}: expected a front-end rejection, got {observation}");
        Assert.Equal(expectedErrors, string.Join(" | ", observation.Errors));
    }

    [Fact]
    public async Task AnExpressionInsideANestedPattern_IsAFrontEndError()
    {
        // The undeclared-name report's text joins its lines with the platform newline; pin codes and spans.
        var observation = await SixRouteAgreement.OnEveryRouteAsync("F((1 + 1, x)) = x\nF((2, 3))");
        Assert.Equal("parse", observation.Kind);
        Assert.Equal(2, observation.Errors.Count);
        Assert.Equal("UnexpectedToken: Expected ')' but found '+'. @ [1:6, 1:7)", observation.Errors[0]);
        Assert.StartsWith("UndeclaredIdentifier: Identifier 'x' is used in conditional branch 'F'", observation.Errors[1], StringComparison.Ordinal);
        Assert.EndsWith(" @ [1:17, 1:18)", observation.Errors[1], StringComparison.Ordinal);
    }

    // ── 6. The neighbouring pattern diagnostics stay as they are ─────────────────────────────────────

    public static TheoryData<string, string, string> NeighbouringDiagnostics() => new()
    {
        { "a one-binder sequence pattern", "F((x)) = x\nF(7)", Singleton + " @ [1:3, 1:6)" },
        { "a sequence pattern whose one item is ()", "F((())) = 1\nF(())", Singleton + " @ [1:3, 1:7)" },
        { "a sequence pattern whose one item is []", "F(([])) = 1\nF([])", Singleton + " @ [1:3, 1:7)" },
        { "two () heads", "F(()) = 1\nF(()) = 2\nF(())", "DuplicateBranchPattern: Duplicate branch pattern for conditional algorithm 'F'. @ [2:1, 2:10)" },
        { "two [] heads", "F([]) = 1\nF([]) = 2\nF([])", "DuplicateBranchPattern: Duplicate branch pattern for conditional algorithm 'F'. @ [2:1, 2:10)" },
    };

    [Theory]
    [MemberData(nameof(NeighbouringDiagnostics))]
    public async Task NeighbouringPatternDiagnostics_AreUnchanged(string label, string source, string expectedErrors)
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.True(observation.Kind == "parse", $"{label}: expected a front-end rejection, got {observation}");
        Assert.Equal(expectedErrors, string.Join(" | ", observation.Errors));
    }

    private static string Outcome(SixRouteAgreement.Observation observation)
        => observation.Kind == "ok" ? $"ok {observation.Value}" : $"{observation.Kind} {string.Join(" | ", observation.Errors)}";

    [Theory]
    [InlineData("x.y")]
    [InlineData("x:0")]
    [InlineData("g(1, 2)")]
    [InlineData("{ 1 }")]
    [InlineData("1 == 1")]
    [InlineData("-x")]
    [InlineData("x*")]
    [InlineData("[count([])]")]
    public async Task OtherExpressionForms_AreRejectedInTheHead(string head)
    {
        // The policy pins rejection in the head, without depending on recovery's secondary diagnostics.
        var source = $"F({head}) = 1";
        var parsed = Parser.Parse(source);
        Assert.True(parsed.HasErrors);
        Assert.Contains(parsed.Diagnostics, d => d.Severity == DiagnosticSeverity.Error && d.Span is { Start.Line: 1 });
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("parse", observation.Kind);
        Assert.NotEmpty(observation.Errors);
    }
}
