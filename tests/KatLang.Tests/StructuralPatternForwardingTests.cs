using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// FORWARDING REBUILDS EACH STRUCTURAL PATTERN AS ITS OWN KIND (FWD-02 with the structural-pattern
/// model).
///
/// <para>Every synthesized call — an exact alias <c>A = S</c>, bare forwarding <c>G(params) = S</c>, a
/// formula that lifts <c>S</c> — forwards every binding as ITSELF (a fixed binding as one read, a
/// collecting binding re-spread) and rebuilds each structural pattern it reconstructs as the SAME
/// KIND: a sequence pattern <c>(…)</c> as a sequence, a list pattern <c>[…]</c> as a list — never
/// the other kind. WHICH bindings fill a pattern depends on the form: an alias inherits the callee's
/// patterns and rebuilds them from its own bindings; bare forwarding fills a callee pattern only from
/// a binding with the same name AND the same pattern (<c>G([x]) = Single</c> forwards
/// <c>Single([x])</c>, while <c>G(x) = Single</c> is rejected — a same-named leaf never reshapes an
/// argument); a formula rebuilds the callee's patterns around the caller's bindings of the same
/// names (by binding name) — a lifted SEQUENCE group left with one non-collecting item is that item
/// (no one-item sequence exists), a lifted list group keeps its brackets.</para>
///
/// <para>Evidence: the elaborated tree itself, equality with the explicit call on six execution routes
/// (<see cref="RepeatedNameConstraintTests.OnEveryRouteAsync"/>), a formula list lift over a corpus
/// of both kinds, and the editor model. Alias transparency itself — <c>A(v) ≡ S(v)</c> over a corpus
/// of callee shapes and supplies — is <see cref="AliasAndBareForwardingTests"/>. Lean evaluates the
/// same elaborated trees through the derived programs of the spec cases,
/// <c>CoreTests/AliasForwarding.lean</c> and <c>CoreTests/RepeatedNameConstraints.lean</c>.</para>
/// </summary>
public class StructuralPatternForwardingTests
{
    private static Task<RepeatedNameConstraintTests.Observation> OnEveryRoute(string source, long? seed = null)
        => RepeatedNameConstraintTests.OnEveryRouteAsync(source, seed);

    /// <summary>The outcome's error code for a failure (<c>err ArityMismatch</c>), the whole outcome otherwise.</summary>
    private static string Kind(string outcome)
        => outcome.StartsWith("err ", StringComparison.Ordinal) ? outcome[..outcome.IndexOf(':', StringComparison.Ordinal)] : outcome;

    private static string CalleeName(string declaration) => declaration[..declaration.IndexOf('(', StringComparison.Ordinal)];

    // ── 1. The elaborated tree: kind-preserving reconstruction ──────────────────────────

    /// <summary>A synthesized argument list as written: <c>[x]</c>, <c>(x, y)</c>, <c>rest*</c>, <c>()</c>.</summary>
    private static string Arguments(IEnumerable<Expr> arguments)
        => string.Join(", ", arguments.Select(static argument => argument switch
        {
            Expr.Param param => param.Name,
            Expr.SequenceSpread spread => Arguments([spread.Operand]) + "*",
            Expr.ListLiteral list => "[" + Arguments(list.Items) + "]",
            Expr.Capture capture => "(" + Arguments(capture.Body) + ")",
            Expr.EmptySequence => "()",
            _ => argument.GetType().Name,
        }));

    private static IEnumerable<(string Name, Algorithm.User Algorithm)> UserProperties(Algorithm.User owner)
    {
        foreach (var property in owner.Properties)
        {
            if (property.Value is not Algorithm.User user)
                continue;
            yield return (property.Name, user);
            foreach (var nested in UserProperties(user))
                yield return nested;
        }
    }

    private static Algorithm.User Owner(Algorithm.User root, string name)
        => Assert.Single(UserProperties(root), property => property.Name == name).Algorithm;

    private static Expr.Call CallTo(Algorithm.User owner, string callee)
    {
        var calls = new List<Expr.Call>();
        var pending = new Stack<Expr>(owner.Output);
        while (pending.TryPop(out var expr))
        {
            if (expr is Expr.Call { Function: Expr.Resolve resolve } match && resolve.Name == callee)
                calls.Add(match);
            IEnumerable<Expr> children = expr switch
            {
                Expr.Call call => [call.Function, .. call.Args],
                Expr.Binary binary => [binary.Left, binary.Right],
                Expr.Index index => [index.Target, index.Selector],
                Expr.ListLiteral list => list.Items,
                Expr.Capture capture => capture.Body,
                Expr.SequenceSpread spread => [spread.Operand],
                _ => [],
            };
            foreach (var child in children)
                pending.Push(child);
        }

        return Assert.Single(calls);
    }

    public static TheoryData<string, string, string, string, string> ElaboratedCalls => new()
    {
        // program, owner, callee, owner's signature, synthesized arguments
        // An alias inherits a repeated name inside a group verbatim, never deduplicated.
        { "P((x, x)) = x\nSome = P", "Some", "P", "(x, x)", "(x, x)" },
        { "P(x, [x, a]) = a\nSome = P", "Some", "P", "x, [x, a]", "x, [x, a]" },
        // A formula lifts by binding name: the callee's pattern rebuilt around the caller's bindings.
        { "E(()) = 0\nA = E + 0", "A", "E", "", "()" },
        { "E([]) = 0\nA = E + 0", "A", "E", "", "[]" },
        { "Single([x]) = x\nQ = Single + 0", "Q", "Single", "[x]", "[x]" },
        { "Add((x, y)) = x + y\nL = [Add]", "L", "Add", "(x, y)", "(x, y)" },
        { "P((a, b)) = a + b\nF(a) = {\n  G = P + 0\n  G(5)\n}", "G", "P", "b", "(a, b)" },
        { "P(x, ((x, a), b)) = a\nSome = [P]:0", "Some", "P", "x, (a, b)", "x, ((x, a), b)" },
        { "P(x, (x, *rest)) = rest\nSome = [P]:0", "Some", "P", "x, (*rest)", "x, (x, rest*)" },
        // Bare forwarding supplies each callee pattern from the SAME-NAMED binding declared with the
        // SAME pattern, rebuilt as its own kind at every depth; unused source parameters stay unused.
        { "C((*xs)) = xs\nG((*xs)) = C", "G", "C", "(*xs)", "(xs*)" },
        { "M([first, *middle, last]) = first\nG([first, *middle, last]) = M", "G", "M", "[first, *middle, last]", "[first, middle*, last]" },
        { "F(([x, y], z)) = x\nG(([x, y], z)) = F", "G", "F", "([x, y], z)", "([x, y], z)" },
        { "Id(v) = v\nG(v, [first, *middle, last]) = Id", "G", "Id", "v, [first, *middle, last]", "v" },
        // A local alias is an alias: it ignores the enclosing binding of the callee's binder name,
        // and the enclosing list forwards its own same-pattern [x] to it.
        { "Single([x]) = x\nF([x]) = {\n  K = Single\n  K\n}", "K", "Single", "[x]", "[x]" },
        { "Single([x]) = x\nF([x]) = {\n  K = Single\n  K\n}", "F", "K", "[x]", "[x]" },
    };

    /// <summary>
    /// The owner's signature is inherited (an alias), written (bare forwarding) or lifted by name (a
    /// formula), and the synthesized call rebuilds every structural pattern it reconstructs — at
    /// every depth — as its OWN kind: a sequence pattern as the tree the written sequence has (a
    /// capture, <c>()</c>, or a lone item itself), a list pattern as a list literal. No kind is
    /// ever converted.
    /// </summary>
    [Theory]
    [MemberData(nameof(ElaboratedCalls))]
    public void TheSynthesizedCallRebuildsEachPatternAsItsOwnKind(
        string program, string owner, string callee, string signature, string expectedArguments)
    {
        var root = SourceProvenance.ParseValid(program + "\n0").Root;
        var algorithm = Owner(root, owner);
        Assert.Equal(signature, string.Join(", ", algorithm.ParameterPatterns.Select(static pattern => pattern.DisplayName)));
        Assert.Equal(expectedArguments, Arguments(CallTo(algorithm, callee).Args));
    }

    /// <summary>
    /// A structural group that binds no name gives FORMULA lifting — which forwards by binding name —
    /// nothing to forward: it rebuilds the group as the one empty structure of its own kind, so
    /// <c>L = [E]</c> takes no parameter and holds <c>[E((), [])]</c> (an alias keeps the groups as
    /// parameters instead, <see cref="AliasAndBareForwardingTests"/>).
    /// </summary>
    [Fact]
    public async Task ZeroCaptureGroups_AreRebuiltEmptyByAFormula()
    {
        const string declaration = "E((), []) = 1\n";
        var formula = Owner(SourceProvenance.ParseValid(declaration + "L = [E]\n0").Root, "L");
        Assert.Empty(formula.ParameterPatterns);
        Assert.Equal("(), []", Arguments(CallTo(formula, "E").Args));
        Assert.Equal("ok L[1]", (await OnEveryRoute(declaration + "L = [E]\nL")).Outcome);
    }

    // ── 2. Bare forwarding needs the same name AND the same pattern ─────────────────────

    public static TheoryData<string, string> ExistingBindings => new()
    {
        // The explicit call passes G's whole x, so a scalar reaches Single's list pattern.
        { "Single([x]) = x\nG(x) = Single(x)\nG(7)", "err TypeMismatch" },
        { "Single([x]) = x\nG([x]) = Single\nG([[7]]) == [7], Single([[7]]) == [7]", "ok S[true, true]" },
        // A local alias keeps Single's [x]; F forwards its own [x] to it by name.
        { "Single([x]) = x\nF([x]) = {\n  K = Single\n  K\n}\nF([[7]])", "ok L[7]" },
        // A collecting stream forwards into the same-named collector of the same pattern.
        { "C((*xs)) = xs\nG((*xs)) = C\nG((1, 2)), G(())", "ok S[L[1, 2], L[]]" },
        { "LC([*xs]) = xs\nUse([*xs]) = LC\nUse([1, 2]), Use([7]), Use([])", "ok S[L[1, 2], L[7], L[]]" },
        { "LC([*xs]) = xs\nUse([*xs]) = LC\nUse(7)", "err TypeMismatch" },
    };

    [Theory]
    [MemberData(nameof(ExistingBindings))]
    public async Task BareForwardingForwardsTheSamePattern(string program, string expected)
        => Assert.Equal(expected, Kind((await OnEveryRoute(program)).Outcome));

    [Theory]
    [InlineData("Single([x]) = x\nG([x]) = Single", "Single([x]) = x\nG([x]) = Single([x])", "7")]
    [InlineData("C((*xs)) = xs\nG((*xs)) = C", "C((*xs)) = xs\nG((*xs)) = C((xs*))", "(1, 2)")]
    [InlineData("C((*xs)) = xs\nG((*xs)) = C", "C((*xs)) = xs\nG((*xs)) = C((xs*))", "7")]
    [InlineData("LC([*xs]) = xs\nUse([*xs]) = LC", "LC([*xs]) = xs\nUse([*xs]) = LC([xs*])", "7")]
    [InlineData("P((x, x)) = x\nSome = P", "P((x, x)) = x\nSome((x, x)) = P((x, x))", "(7, 7)")]
    [InlineData("P((x, x)) = x\nSome = P", "P((x, x)) = x\nSome((x, x)) = P((x, x))", "(7, 8)")]
    [InlineData("P(x, [x, a]) = a\nSome = P", "P(x, [x, a]) = a\nSome(x, [x, a]) = P(x, [x, a])", "1, [1, 2]")]
    public async Task ImplicitForwarding_IsObservationallyTheExplicitCall(string implicitProgram, string explicitProgram, string arguments)
    {
        var owner = implicitProgram.Split('\n')[^1].Split(['(', ' ', '='], StringSplitOptions.RemoveEmptyEntries)[0];
        var implicitObservation = await OnEveryRoute($"{implicitProgram}\n{owner}({arguments})");
        var explicitObservation = await OnEveryRoute($"{explicitProgram}\n{owner}({arguments})");
        Assert.Equal(Kind(explicitObservation.Outcome), Kind(implicitObservation.Outcome));
    }

    // ── 3. Editor model: the rebuilt group creates no site ────────────────────────────

    [Fact]
    public void TheRebuiltGroupCreatesNoEditorSite()
    {
        const string source = "Single([x]) = x\nA = Single\nA([[7]])";
        var model = SemanticModelBuilder.Build(SourceProvenance.ParseValid(source).Parsed);
        var lines = source.Split('\n');
        var occurrences = model.IdentifierOccurrences.Concat(model.Declarations).ToList();
        foreach (var occurrence in occurrences)
        {
            Assert.Equal(occurrence.Span.Start.Line, occurrence.Span.End.Line);
            var line = lines[occurrence.Span.Start.Line - 1];
            Assert.Equal(occurrence.Name, line[(occurrence.Span.Start.Column - 1)..(occurrence.Span.End.Column - 1)]);
        }

        // The written `x`s only: the list-pattern binder of Single and its body reference.
        Assert.Equal(
            [new SourcePosition(1, 9), new SourcePosition(1, 15)],
            occurrences.Where(static occurrence => occurrence.Name == "x").Select(static occurrence => occurrence.Span.Start).Distinct().Order());
        Assert.Equal("Single", model.FindResolutionAt(new SourcePosition(2, 5))?.ResolvedProperty?.Name);
    }

    // ── 4. The metamorphic property over a corpus of both kinds ──────────────────────

    private static readonly string[] Callees =
    [
        "Single([x]) = x",
        "Pair((x, y)) = x, y",
        "LPair([x, y]) = x, y",
        "C((*xs)) = xs.count",
        "LC([*xs]) = xs",
        "F((first, *rest)) = first, rest",
        "LF([first, *rest]) = first, rest",
        "Mid((first, *middle, last)) = first, middle, last",
        "LMid([first, *middle, last]) = first, middle, last",
        "SL(([x, y], z)) = x, y, z",
        "LS([(x, y), z]) = x, y, z",
        "Nest([[x]]) = x",
        "Rest([(x, *r), *s]) = x, r, s",
        "Kinds([x], (y, z)) = x, y, z",
        "Mixed(a, [b]) = a, b",
    ];

    private static readonly string[] CorpusValues =
    [
        "7", "'a'", "true", "()", "[]",
        "(1, 2)", "(1, 2, 3)", "((1, 2), 3)", "((1, 2), (3, 4))", "([1, 2], 3)",
        "[7]", "[1, 2]", "[1, 2, 3]", "[[7]]", "[(1, 2)]", "[()]", "[[]]", "[(1, 2), 3]", "[[1, 2], 3]",
        "[(1, 2, 3), 4]", "[1], (2, 3)", "0, [7]",
    ];

    public static TheoryData<int> CorpusCallees()
    {
        var data = new TheoryData<int>();
        for (var index = 0; index < Callees.Length; index++)
            data.Add(index);
        return data;
    }

    /// <summary>
    /// THE FORMULA LAW over structural callees: the list lift <c>L = [callee]</c> — formula lifting
    /// by binding name, which copies the callee's patterns and rebuilds each as its own kind — is the
    /// written <c>[callee(args)]</c> for every structural shape of both kinds and every input, on
    /// every route: the same outcome kind and the same host calls.
    /// </summary>
    [Theory]
    [MemberData(nameof(CorpusCallees))]
    public async Task EveryFormulaListLiftOfTheCorpus_IsTheWrittenCall(int calleeIndex)
    {
        var declaration = Callees[calleeIndex];
        var callee = CalleeName(declaration);
        foreach (var arguments in CorpusValues)
        {
            var directList = await OnEveryRoute($"{declaration}\n[{callee}({arguments})]");
            var listLift = await OnEveryRoute($"{declaration}\nL = [{callee}]\nL({arguments})");
            Assert.True(
                Kind(directList.Outcome) == Kind(listLift.Outcome) && directList.HostCalls.SequenceEqual(listLift.HostCalls),
                $"{declaration} with ({arguments})\n[direct]: {directList}\nlist lift: {listLift}");
        }
    }
}
