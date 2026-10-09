using System.Globalization;
using System.Text.RegularExpressions;

namespace KatLang.Tests;

/// <summary>
/// Q-33 (decided 2026-10-09): THE LINE-FINAL STAR IS NO EXCEPTION. A <c>*</c> at the end of a
/// physical line is classified by SYN-11 exactly like any other star: if the next significant token
/// — across blank lines and comments — can begin an operand and does not begin a declaration, the
/// star is binary multiplication, and expression parsing continues across the newline (SYN-08) with
/// ordinary operator precedence unchanged; otherwise the existing spread rules apply. The layout
/// alone produces no warning and no error, so <c>X = A*</c> newline <c>X</c> is <c>X = A * X</c>
/// with no output row. A spread ROW meant to end there takes <c>A*,</c>; a definition BODY ending
/// in a spread is closed as <c>X = (A*)</c> or <c>X = { A* }</c> (a trailing comma would continue
/// the body); a closing delimiter, the end of input or a following declaration head also ends it.
///
/// <para>The suite contains 250 cases that verify structural parsing and nine negative cases that
/// verify diagnostic codes, explanations and exact source spans. Valid-source cases also require
/// an empty diagnostic list at every severity; negative cases assert the expected diagnostics
/// instead. Values are observed on the six routes of
/// <see cref="SixRouteAgreement"/>. T1 compositional contexts × layouts, T2 the explicit spread
/// endings, T3 the canonical witness, T4 multiline multiplication and precedence, T5 identifier
/// independence, T6 modules and deferred branches, T7 the diagnostics of genuinely misplaced spreads.
/// Pinned elsewhere too: <c>StarSyntaxTests</c> (the SYN-07B layout section), the spec cases
/// <c>star-before-*</c> and <c>line-final-star-in-definition-continues</c>.</para>
/// </summary>
public class LineFinalStarLawTests
{
    private const string Definitions = "A = 4\nB = 6\n";
    private const string Lib = "https://katlang.org/q33/lib.kat";

    // ── Tree rendering ───────────────────────────────────────────────────────

    /// <summary>
    /// A span-free, precedence-revealing spelling of an elaborated tree: every operator node is
    /// written in prefix form with its children in parentheses, so two different groupings can
    /// never share a shape string.
    /// </summary>
    private static string Shape(Expr expr) => expr switch
    {
        Expr.Binary(var op, var left, var right) => $"{ExprNameRenderer.BinaryOpText(op)}({Shape(left)}, {Shape(right)})",
        Expr.Comparison chain => "cmp(" + Shape(chain.First)
            + string.Concat(chain.Links.Select(link => $" {ExprNameRenderer.ComparisonOpText(link.Op)} {Shape(link.Operand)}")) + ")",
        Expr.Unary(UnaryOp.Not, var operand) => $"not({Shape(operand)})",
        Expr.Unary(_, var operand) => $"neg({Shape(operand)})",
        Expr.SequenceSpread(var operand) => $"spread({Shape(operand)})",
        Expr.Capture(var body) => $"capture({Join(body)})",
        Expr.ListLiteral(var items) => $"list({Join(items)})",
        Expr.Index(var target, var selector) => $"index({Shape(target)}, {Shape(selector)})",
        Expr.Call(var function, var args) => $"call({Shape(function)}; {Join(args)})",
        Expr.DotCall dot => dot.Args is { } args
            ? $"dot({Shape(dot.Target)}.{dot.Name}; {Join(args)})"
            : $"dot({Shape(dot.Target)}.{dot.Name})",
        Expr.AlgorithmExpr(var algorithm) => $"block({AlgorithmShape(algorithm)})",
        Expr.Resolve(var name) => name,
        Expr.Param(var name) => "$" + name,
        Expr.Num(var value) => value.ToString(CultureInfo.InvariantCulture),
        Expr.BoolLiteral(var value) => value ? "true" : "false",
        _ => $"<{expr.GetType().Name}>",
    };

    private static string Join(IEnumerable<Expr> items) => string.Join(", ", items.Select(Shape));

    private static string Rows(Algorithm algorithm)
        => string.Join(" | ", Assert.IsType<Algorithm.User>(algorithm).Output.Select(Shape));

    private static string AlgorithmShape(Algorithm algorithm) => algorithm switch
    {
        Algorithm.User user => (user.Properties.Count == 0
                ? ""
                : "{" + string.Join("; ", user.Properties.Select(p => $"{p.Name} = {AlgorithmShape(p.Value)}")) + "} ")
            + string.Join(" | ", user.Output.Select(Shape)),
        Algorithm.Conditional family => "family[" + string.Join(" / ", family.Branches.Select(b => AlgorithmShape(b.Body))) + "]",
        _ => $"<{algorithm.GetType().Name}>",
    };

    /// <summary>Every property and every root row: the whole program's source boundaries at once.</summary>
    private static string ProgramShape(Algorithm.User root) => AlgorithmShape(root);

    private static Algorithm Body(Algorithm owner, string name)
        => Assert.Single(owner.Properties, p => p.Name == name).Value;

    private static SourceProvenance ParseWithoutAnyDiagnostic(string source)
    {
        var parsed = SourceProvenance.ParseValid(source);
        // Q-33: the layout is valid source and carries NO diagnostic of any severity — no error,
        // warning, information or hint.
        Assert.True(parsed.Diagnostics.Count == 0,
            $"expected no diagnostic at all, got: {string.Join(" | ", parsed.Diagnostics.Select(d => $"{d.Severity} {d.Code}: {d.Message}"))}\nsource:\n{source}");
        Assert.Empty(Parser.ParseSyntax(source).Diagnostics.ToArray());
        return parsed;
    }

    private static async Task<string> ValueOnEveryRoute(string source)
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.True(observation.Kind == "ok", $"expected success, got {observation}\nsource:\n{source}");
        return observation.Value!;
    }

    // ── T1: one law in every context, for every layout ───────────────────────

    /// <summary>The product <c>A * B</c> in every spelling. The first is the reference.</summary>
    private static readonly Dictionary<string, string> Layouts = new(StringComparer.Ordinal)
    {
        ["same line, detached"] = "A * B",
        ["same line, attached"] = "A* B",
        ["LF, attached"] = "A*\nB",
        ["LF, detached"] = "A *\nB",
        ["CRLF, attached"] = "A*\r\nB",
        ["CRLF, detached"] = "A *\r\nB",
        ["trailing spaces after the star"] = "A*   \nB",
        ["tab-indented operand"] = "A*\n\tB",
        ["space-indented operand"] = "A*\n        B",
        ["comment after the star"] = "A* # the operand follows\nB",
        ["blank lines"] = "A*\n\n\nB",
        ["comment-only line between"] = "A*\n# the operand follows\nB",
        ["CRLF, blank line, comment, tab"] = "A*\r\n\r\n# note\r\n\tB",
        ["detached, comment, blank line"] = "A * # note\n\nB",
    };

    private sealed record Context(string Template, Func<Algorithm.User, string> Locate, string ExpectedShape, string ExpectedValue);

    /// <summary>
    /// Where the product stands. <see cref="Context.Locate"/> renders the product's host AND the
    /// surrounding rows, so a continuation that swallowed or released the wrong line changes it.
    /// </summary>
    private static readonly Dictionary<string, Context> Contexts = new(StringComparer.Ordinal)
    {
        ["root row"] = new(
            Definitions + "{P}",
            static root => $"rows: {Rows(root)}",
            "rows: *(A, B)", "24"),
        ["definition body"] = new(
            Definitions + "X = {P}\nX",
            static root => $"X: {Rows(Body(root, "X"))}; rows: {Rows(root)}",
            "X: *(A, B); rows: X", "24"),
        ["clause branch body"] = new(
            Definitions + "F(0) = 0\nF(n) = {P}\nF(1)",
            static root => $"F: {AlgorithmShape(Body(root, "F"))}; rows: {Rows(root)}",
            "F: family[0 / *(A, B)]; rows: call(F; 1)", "24"),
        ["deconstruction right-hand side"] = new(
            Definitions + "x, y = {P}, 1\nx",
            static root => $"rhs: {Rows(Assert.Single(root.Properties, p => p.Name.StartsWith("$deconstruct", StringComparison.Ordinal)).Value)}; rows: {Rows(root)}",
            "rhs: *(A, B) | 1; rows: x", "24"),
        ["brace block row"] = new(
            Definitions + "{ {P} }",
            static root => $"rows: {Rows(root)}",
            "rows: block(*(A, B))", "24"),
        ["brace definition body"] = new(
            Definitions + "X = {\n  {P}\n}\nX",
            static root => $"X: {Rows(Body(root, "X"))}; rows: {Rows(root)}",
            "X: *(A, B); rows: X", "24"),
        ["parenthesized operand"] = new(
            Definitions + "1 + ({P})",
            static root => $"rows: {Rows(root)}",
            "rows: +(1, *(A, B))", "25"),
        ["list element"] = new(
            Definitions + "[{P}]",
            static root => $"rows: {Rows(root)}",
            "rows: list(*(A, B))", "L[24]"),
        ["argument"] = new(
            Definitions + "F(x) = x\nF({P})",
            static root => $"rows: {Rows(root)}",
            "rows: call(F; *(A, B))", "24"),
        ["first of two arguments"] = new(
            Definitions + "G(x, y) = x - y\nG({P}, 1)",
            static root => $"rows: {Rows(root)}",
            "rows: call(G; *(A, B), 1)", "23"),
        ["callback body"] = new(
            Definitions + "map([1, 2], { {P} + x })",
            static root => $"rows: {Rows(root)}",
            "rows: call(map; list(1, 2), block(+(*(A, B), $x)))", "L[25, 26]"),
        ["inline module member"] = new(
            "M = { public A = 4\n  public B = 6\n  public X = {P}\n  0 }\nM.X",
            static root => $"M.X: {Rows(Body(Body(root, "M"), "X"))}; M rows: {Rows(Body(root, "M"))}; rows: {Rows(root)}",
            "M.X: *(A, B); M rows: 0; rows: dot(M.X)", "24"),
    };

    public static TheoryData<string, string> ContextsByLayout()
    {
        var data = new TheoryData<string, string>();
        foreach (var context in Contexts.Keys)
        {
            foreach (var layout in Layouts.Keys)
                data.Add(context, layout);
        }

        return data;
    }

    private static string Program(string context, string layout)
        => Contexts[context].Template.Replace("{P}", Layouts[layout], StringComparison.Ordinal);

    [Theory]
    [MemberData(nameof(ContextsByLayout))]
    public async Task LineFinalStar_IsClassifiedLikeEveryStar_InEveryContextAndLayout(string context, string layout)
    {
        var source = Program(context, layout);
        var parsed = ParseWithoutAnyDiagnostic(source);

        // The product is ONE multiplication node whose right operand is exactly `B`, and every
        // surrounding row and declaration stays where it was written.
        Assert.Equal(Contexts[context].ExpectedShape, Contexts[context].Locate(parsed.Root));

        // Layout independence: the elaborated program is the very program of the one-line
        // `A * B` spelling (the encoder is span-free), and so is its value on every route.
        var reference = SourceProvenance.ParseValid(Program(context, "same line, detached"));
        Assert.Equal(LeanAstEncoder.EncodeProgram(reference.Root), LeanAstEncoder.EncodeProgram(parsed.Root));
        Assert.Equal(Contexts[context].ExpectedValue, await ValueOnEveryRoute(source));
    }

    // ── T2: the explicit spread endings ──────────────────────────────────────

    public static TheoryData<string, string, string> SpreadEndings() => new()
    {
        // A comma ends the spread slot; the next line is a row of its own.
        { "A = (1, 2)\nB = 5\nA*,\nB", "{A = capture(1, 2); B = 5} spread(A) | B", "S[1, 2, 5]" },
        { "A = (1, 2)\nB = 5\nA*, # end of the spread row\r\nB", "{A = capture(1, 2); B = 5} spread(A) | B", "S[1, 2, 5]" },
        { "A = (1, 2)\nB = 5\nA*\n, B", "{A = capture(1, 2); B = 5} spread(A) | B", "S[1, 2, 5]" },
        // Structural closing of a spread-ending definition body.
        { "A = (1, 2)\nB = 5\nX = (A*)\nB\nX", "{A = capture(1, 2); B = 5; X = capture(spread(A))} B | X", "S[5, S[1, 2]]" },
        { "A = (1, 2)\nB = 5\nX = { A* }\nB\nX", "{A = capture(1, 2); B = 5; X = spread(A)} B | X", "S[5, S[1, 2]]" },
        // A following declaration head is never an operand: every head form ends the expression.
        { "A = (1, 2)\nA*\nB = 5\nB", "{A = capture(1, 2); B = 5} spread(A) | B", "S[1, 2, 5]" },
        { "A = (1, 2)\nA*\npublic B = 5\nB", "{A = capture(1, 2); B = 5} spread(A) | B", "S[1, 2, 5]" },
        { "A = (1, 2)\nA*\nF(x) = x + 3\nF(2)", "{A = capture(1, 2); F = +($x, 3)} spread(A) | call(F; 2)", "S[1, 2, 5]" },
        { "A = (1, 2)\nA*\nx, y = 4, 5\ny", "{A = capture(1, 2); $deconstruct$0 = 4 | 5; x = call(block($x); $deconstruct$0); y = call(block($y); $deconstruct$0)} spread(A) | y", "S[1, 2, 5]" },
        { "A = (1, 2)\nA*\n*items = 4, 5\nitems:1", "{A = capture(1, 2); $deconstruct$0 = 4 | 5; items = call(block($items); $deconstruct$0)} spread(A) | index(items, 1)", "S[1, 2, 5]" },
        { "A = (1, 2)\nX = A*\nY = 5\nX, Y", "{A = capture(1, 2); X = spread(A); Y = 5} X | Y", "S[S[1, 2], 5]" },
        { "A = (1, 2)\n{ A*\n  Y = 5\n  Y }", "{A = capture(1, 2)} block({Y = 5} spread(A) | Y)", "S[1, 2, 5]" },
        // A closing delimiter or the end of input closes the expression before any operand.
        { "A = (1, 2)\n(A*\n)", "{A = capture(1, 2)} capture(spread(A))", "S[1, 2]" },
        { "A = (1, 2)\n[A*\n]", "{A = capture(1, 2)} list(spread(A))", "L[1, 2]" },
        { "A = (1, 2)\n{ A*\n}", "{A = capture(1, 2)} block(spread(A))", "S[1, 2]" },
        { "Coll(*xs) = xs\nA = (1, 2)\nColl(A*\n)", "{A = capture(1, 2); Coll = $xs} call(Coll; spread(A))", "L[1, 2]" },
        { "A = (1, 2)\nA*", "{A = capture(1, 2)} spread(A)", "S[1, 2]" },
        { "A = (1, 2)\nA* # the end\n\n# nothing follows", "{A = capture(1, 2)} spread(A)", "S[1, 2]" },
        { "A = (1, 2)\nX\nX = A*", "{A = capture(1, 2); X = spread(A)} X", "S[1, 2]" },
        // Tokens that cannot begin a multiplication operand.
        { "A = (1, 2)\nA*\nnot true", "{A = capture(1, 2)} spread(A) | not(true)", "S[1, 2, false]" },
        { "Coll(*xs) = xs\nA = (1, 2)\nA*\n.Coll", "{A = capture(1, 2); Coll = $xs} call(Coll; spread(A))", "L[1, 2]" },
    };

    [Theory]
    [MemberData(nameof(SpreadEndings))]
    public async Task SpreadEnding_ProducesTheSpreadNode_AndKeepsTheNextRowSeparate(string source, string expectedProgram, string expectedValue)
    {
        var parsed = ParseWithoutAnyDiagnostic(source);
        Assert.Equal(expectedProgram, ProgramShape(parsed.Root));
        Assert.Equal(expectedValue, await ValueOnEveryRoute(source));
    }

    [Fact]
    public async Task TrailingCommaInADefinitionBody_ContinuesTheBody_SoItEndsARowButNotABody()
    {
        // The comma ends the spread SLOT, but a trailing comma continues the line-bounded body, so
        // the next row becomes the body's next slot. A spread ROW ends with `A*,`; a definition body
        // that ends in a spread is closed structurally instead (`X = (A*)`, `X = { A* }`, above).
        const string source = "A = (1, 2)\nX = A*,\n3\nX";
        var parsed = ParseWithoutAnyDiagnostic(source);
        Assert.Equal("{A = capture(1, 2); X = spread(A) | 3} X", ProgramShape(parsed.Root));
        Assert.Equal("S[1, 2, 3]", await ValueOnEveryRoute(source));
    }

    // ── T3: the canonical witness ────────────────────────────────────────────

    [Fact]
    public async Task CanonicalWitness_ContinuesTheDefinition_LeavesNoOutputRow_AndReportsNothing()
    {
        const string source = "A = 2\nX = A*\nX";
        var parsed = ParseWithoutAnyDiagnostic(source);

        // X = A * X: `X` begins an operand and no declaration, so the star multiplies and the
        // definition continues across the newline; no root row remains.
        Assert.Equal("*(A, X)", Rows(Body(parsed.Root, "X")));
        Assert.Empty(parsed.Root.Output);

        // The engine paths report the ordinary no-output result; the evaluator paths report the
        // missing output underneath it (the established host-API layering). Nothing else.
        var none = Assert.IsType<RunResult.NoProgramOutput>(KatLangEngine.Run(source));
        Assert.Equal(KatLangErrorCode.MissingOutput, none.Diagnostic.Code);
        foreach (var route in SixRouteAgreement.Routes)
        {
            var observation = await SixRouteAgreement.ObserveAsync(route, source);
            if (route is SixRouteAgreement.Route.EngineSync or SixRouteAgreement.Route.EngineAsync or SixRouteAgreement.Route.EngineAsyncTwin)
                Assert.Equal("none", observation.Kind);
            else
                Assert.Equal("err", observation.Kind);
            Assert.StartsWith("MissingOutput", Assert.Single(observation.Errors), StringComparison.Ordinal);
        }
    }

    [Fact]
    public async Task CanonicalWitness_WithANumberRow_MultipliesItIntoTheDefinition()
    {
        const string source = "A = 2\nX = A*\n3\nX";
        var parsed = ParseWithoutAnyDiagnostic(source);
        Assert.Equal("*(A, 3)", Rows(Body(parsed.Root, "X")));
        Assert.Equal("X", Rows(parsed.Root));
        Assert.Equal("6", await ValueOnEveryRoute(source));
    }

    // ── T4: multiline multiplication keeps ordinary precedence ───────────────

    public static TheoryData<string, string, string> MultilineProducts() => new()
    {
        { "A = 4\nB = 6\nA*\n(B + 1)", "*(A, +(B, 1))", "28" },
        { "A = 4\nB = 6\nA *\n(B + 1)", "*(A, +(B, 1))", "28" },
        // The continuation is token-level: the next line is NOT one operand.
        { "A = 4\nB = 6\nA*\nB + 1", "+(*(A, B), 1)", "25" },
        { "A = 4\nB = 6\nA *\nB - 1", "-(*(A, B), 1)", "23" },
        { "A = 4\nB = 6\nA*\nB ^ 2", "*(A, ^(B, 2))", "144" },
        { "A = 4\nB = 6\nA*\n-B", "*(A, neg(B))", "-24" },
        { "A = 4\nL = [6]\nA*\nL:0", "*(A, index(L, 0))", "24" },
        { "A = 4\nB = 6\nA*\nB == 24", "cmp(*(A, B) == 24)", "true" },
        { "A = 4\nB = 6\nC = 2\nA*\nB*\nC", "*(*(A, B), C)", "48" },
        { "map([1, 2], { x*\n  (x + 1) })", "call(map; list(1, 2), block(*($x, +($x, 1))))", "L[2, 6]" },
        { "map([1, 2], { x *\n  10 })", "call(map; list(1, 2), block(*($x, 10)))", "L[10, 20]" },
    };

    [Theory]
    [MemberData(nameof(MultilineProducts))]
    public async Task MultilineMultiplication_IsPreserved_WithOrdinaryPrecedence(string source, string expectedRow, string expectedValue)
    {
        var parsed = ParseWithoutAnyDiagnostic(source);
        Assert.Equal(expectedRow, Rows(parsed.Root));
        Assert.Equal(expectedValue, await ValueOnEveryRoute(source));
    }

    public static TheoryData<string, string, string, string> MultilineDefinitionBodies() => new()
    {
        { "A = 2\nB = 3\nX = A*\nB + 1\nX", "X", "+(*(A, B), 1)", "7" },
        // The deconstruction RHS is `(V * x) + y`, never `V * (x + y)`: precedence is unchanged.
        { "V = [(1, 2)]\nx, y = V*\nx + y\nV", "$deconstruct$0", "+(*(V, x), y)", "L[S[1, 2]]" },
        { "P = {\n  A = 2\n  A*\n  3\n}\nP", "P", "*(A, 3)", "6" },
        { "Area(w, h) = w*\n  h\nArea(3, 4)", "Area", "*($w, $h)", "12" },
        { "Total = Price*\n  Qty\nPrice = 4\nQty = 3\nTotal", "Total", "*(Price, Qty)", "12" },
    };

    [Theory]
    [MemberData(nameof(MultilineDefinitionBodies))]
    public async Task MultilineMultiplication_InADefinitionBody_KeepsOrdinaryPrecedence(
        string source, string property, string expectedBody, string expectedValue)
    {
        var parsed = ParseWithoutAnyDiagnostic(source);
        Assert.Equal(expectedBody, Rows(Body(parsed.Root, property)));
        Assert.Equal(expectedValue, await ValueOnEveryRoute(source));
    }

    // ── T5: identifier independence ──────────────────────────────────────────

    /// <summary>
    /// A consistent renaming, including builtin names used as ordinary properties and a
    /// definition whose continuation names the definition itself. No name takes part in the law.
    /// </summary>
    private static readonly (string From, string To)[] Renaming =
    [
        ("A", "Weight"), ("B", "if"), ("C", "string"), ("X", "count"), ("Y", "Other"),
        ("F", "Scale"), ("G", "Gap"), ("L", "Items"), ("V", "Pairs"), ("M", "Module"),
        ("x", "item"), ("y", "rest"),
    ];

    private static string Rename(string text)
    {
        foreach (var (from, to) in Renaming)
            text = Regex.Replace(text, $@"\b{from}\b", to, RegexOptions.CultureInvariant);
        return text;
    }

    public static TheoryData<string> RenamablePrograms()
    {
        var data = new TheoryData<string>();
        foreach (var context in Contexts.Keys)
        {
            data.Add(Program(context, "LF, attached"));
            data.Add(Program(context, "CRLF, blank line, comment, tab"));
        }

        data.Add("A = 2\nX = A*\nX\n7");
        data.Add("A = 2\nX = A*\n3\nX");
        data.Add("A = 2\nY = 5\nX = A*\nY\nX");
        data.Add("A = 2\nY = 5\nX = A*\nX\nY");
        data.Add("A = 2\nB = 3\nX = A*\nB + 1\nX");
        data.Add("V = [(1, 2)]\nx, y = V*\nx + y\nV");
        data.Add("A = (1, 2)\nB = 5\nX = (A*)\nB\nX");
        data.Add("A = (1, 2)\nA*\nB = 5\nB");
        data.Add("A = (1, 2)\nX = A*\nY = 5\nX, Y");
        return data;
    }

    [Theory]
    [MemberData(nameof(RenamablePrograms))]
    public async Task Renaming_NeverChangesTheContinuation(string source)
    {
        var renamed = Rename(source);
        Assert.NotEqual(source, renamed);
        var original = ParseWithoutAnyDiagnostic(source);
        var parsed = ParseWithoutAnyDiagnostic(renamed);
        Assert.Equal(Rename(ProgramShape(original.Root)), ProgramShape(parsed.Root));

        var before = await SixRouteAgreement.OnEveryRouteAsync(source);
        var after = await SixRouteAgreement.OnEveryRouteAsync(renamed);
        Assert.Equal(before.Kind, after.Kind);
        Assert.Equal(before.Value, after.Value);
    }

    [Fact]
    public void ContinuationOperand_NamingTheDefinitionItself_OrAnotherName_IsTheSameMultiplication()
    {
        Assert.Equal("*(A, X)", Rows(Body(ParseWithoutAnyDiagnostic("A = 2\nY = 5\nX = A*\nX\nY").Root, "X")));
        Assert.Equal("*(A, Y)", Rows(Body(ParseWithoutAnyDiagnostic("A = 2\nY = 5\nX = A*\nY\nX").Root, "X")));
    }

    // ── T6: modules and deferred branches ────────────────────────────────────

    private sealed class CountingModules((string Url, string Source)[] files)
    {
        private readonly Dictionary<string, string> _files = files.ToDictionary(f => f.Url, f => f.Source, StringComparer.Ordinal);

        public Dictionary<string, int> Fetches { get; } = new(StringComparer.Ordinal);

        public RunOptions Options => new()
        {
            DownloadCode = (url, _) =>
            {
                Fetches[url] = Fetches.GetValueOrDefault(url) + 1;
                return _files.TryGetValue(url, out var source)
                    ? ValueTask.FromResult(source)
                    : throw new InvalidOperationException($"404: {url}");
            },
        };
    }

    private static Algorithm.User OpenedModule(Algorithm.User root)
        => Assert.IsType<Algorithm.User>(Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(root.Opens)).Algorithm);

    private static async Task<string> RunAsyncValue(string source, RunOptions options)
    {
        var result = await KatLangEngine.RunAsync(source, options);
        var success = Assert.IsType<RunResult.Success>(result);
        return SixRouteAgreement.Neutral(success.Value);
    }

    private static async Task<SourceProvenance> ParseModuleProgramWithoutAnyDiagnostic(string source, RunOptions options)
    {
        var parsed = await SourceProvenance.ParseValidAsync(source, options);
        Assert.True(parsed.Diagnostics.Count == 0,
            $"expected no diagnostic at all, got: {string.Join(" | ", parsed.Diagnostics.Select(d => $"{d.Severity} {d.Code}: {d.Message}"))}");
        return parsed;
    }

    [Theory]
    [InlineData("public A = 2\npublic X = A*\nY\npublic Y = 3\n0")]
    [InlineData("public A = 2\r\npublic X = A*\r\nY\r\npublic Y = 3\r\n0")]
    [InlineData("public A = 2\npublic X = A*\n\n# continued\n  Y\npublic Y = 3\n0\n")]
    public async Task LoadedModuleText_FollowsTheSameLaw(string module)
    {
        var modules = new CountingModules([(Lib, module)]);
        var parsed = await ParseModuleProgramWithoutAnyDiagnostic($"open '{Lib}'\nX", modules.Options);
        var opened = OpenedModule(parsed.Root);
        Assert.Equal("*(A, Y)", Rows(Body(opened, "X")));
        Assert.Equal("0", Rows(opened));
        Assert.Equal("6", await RunAsyncValue($"open '{Lib}'\nX", new CountingModules([(Lib, module)]).Options));
    }

    [Theory]
    [InlineData("public A = (1, 2)\npublic X = A*")]
    [InlineData("public A = (1, 2)\npublic X = A*\n")]
    [InlineData("public A = (1, 2)\r\npublic X = A*\r\n\r\n# the end of the module\r\n")]
    public async Task ModuleSourceEndingInAStar_EndsAtItsOwnEndOfInput_WhateverTheLoadSiteWritesNext(string module)
    {
        // A module is parsed as its own document: its last line ends at ITS end of input, never
        // continued by the line the load site writes after `load(…)`.
        const string source = $"M = load('{Lib}')\nM.X\n5";
        var parsed = await ParseModuleProgramWithoutAnyDiagnostic(source, new CountingModules([(Lib, module)]).Options);
        var held = Assert.IsType<Algorithm.User>(Body(parsed.Root, "M"));
        Assert.Equal("spread(A)", Rows(Body(held, "X")));
        Assert.Equal("dot(M.X) | 5", Rows(parsed.Root));
        Assert.Equal("S[S[1, 2], 5]", await RunAsyncValue(source, new CountingModules([(Lib, module)]).Options));
    }

    [Fact]
    public async Task UnseparatedSpreadRowInModuleText_IsOneMultiplicationRow()
    {
        // The intentional-multiplication twin of the ModuleCoordinateSpaceTests fixture: without
        // the trailing comma, `F(1, (2, 3))*` before the `[H]:0` line multiplies, so the module has
        // ONE row and no spread node. With `*,` it has the spread row and the selection row.
        const string unseparated = "open Math\npublic F(x, (y, *z)) = x + y\npublic G(0) = 'a'\npublic G(n) = n.count\nH = { a, *b = 1, 2, 3\n a + b.count }\nF(1, (2, 3))*\n[H]:0";
        var separated = unseparated.Replace("F(1, (2, 3))*\n", "F(1, (2, 3))*,\n", StringComparison.Ordinal);
        Assert.NotEqual(unseparated, separated);

        var one = await ParseModuleProgramWithoutAnyDiagnostic($"M = load('{Lib}')\n1", new CountingModules([(Lib, unseparated)]).Options);
        Assert.Equal("*(call(F; 1, capture(2, 3)), index(list(H), 0))", Rows(Body(one.Root, "M")));

        var two = await ParseModuleProgramWithoutAnyDiagnostic($"M = load('{Lib}')\n1", new CountingModules([(Lib, separated)]).Options);
        Assert.Equal("spread(call(F; 1, capture(2, 3))) | index(list(H), 0)", Rows(Body(two.Root, "M")));
    }

    [Fact]
    public async Task DeferredBranch_IsParsedEagerly_UnderTheSameLaw_SelectedOrNot()
    {
        const string module = "public V = 21\n0";
        const string branches = $"F(0) = {{ open '{Lib}'\n  V*\n  2 }}\nF(n) = n\n";

        foreach (var row in new[] { "F(0)", "F(5)" })
        {
            // The load-bearing branch is parsed eagerly with the document: its body multiplies
            // whether or not evaluation ever selects it.
            var raw = SourceProvenance.ParseSyntaxValidRoot(branches + row);
            var family = Assert.IsType<Algorithm.Conditional>(Body(raw, "F"));
            Assert.Equal("*(V, 2)", Rows(family.Branches[0].Body));
            await ParseModuleProgramWithoutAnyDiagnostic(branches + row, new CountingModules([(Lib, module)]).Options);
        }

        // Selected: the deferred unit materializes and multiplies.
        var selected = new CountingModules([(Lib, module)]);
        Assert.Equal("42", await RunAsyncValue(branches + "F(0)", selected.Options));
        Assert.Equal(1, selected.Fetches.GetValueOrDefault(Lib));

        // Never selected: never fetched, and the program runs.
        var unselected = new CountingModules([(Lib, module)]);
        Assert.Equal("5", await RunAsyncValue(branches + "F(5)", unselected.Options));
        Assert.Equal(0, unselected.Fetches.GetValueOrDefault(Lib));
    }

    // ── T7: genuinely misplaced spreads keep their diagnostics ───────────────

    /// <summary>
    /// <c>A*</c> newline <c>B*</c>: the first star multiplies (an operand follows), so the spread
    /// <c>B*</c> becomes its right operand — the existing <c>MisplacedSpread</c>, reported at
    /// that spread with the targeted line-final explanation (F13a), in every context.
    /// </summary>
    public static TheoryData<string, int, int, int, int> SpreadOperandOnALaterLine() => new()
    {
        { "A = 1, 2\nB = 3, 4\nA*\nB*", 4, 1, 4, 3 },
        { "A = 1, 2\nB = 3, 4\nA*\r\nB*", 4, 1, 4, 3 },
        { "A = 1, 2\nB = 3, 4\nA* # note\n\n# more\nB*", 6, 1, 6, 3 },
        { "A = 1, 2\nB = 3, 4\nX = A*\nB*\nY = 5\nX", 4, 1, 4, 3 },
        { "A = 1, 2\nB = 3, 4\n{ A*\n  B* }", 4, 3, 4, 5 },
        { "A = 1, 2\nB = 3, 4\nF(x) = x\nF(A*\n  B*)", 5, 3, 5, 5 },
        { "A = 1, 2\nB = 3, 4\n[A*\nB*]", 4, 1, 4, 3 },
    };

    [Theory]
    [MemberData(nameof(SpreadOperandOnALaterLine))]
    public void SpreadOperandOnALaterLine_KeepsTheTargetedMisplacedSpreadDiagnostic(
        string source, int line, int column, int endLine, int endColumn)
    {
        var error = Assert.Single(SourceProvenance.ExpectFrontEndError(source));
        Assert.Equal(DiagnosticSeverity.Error, error.Severity);
        Assert.Equal(DiagnosticCode.MisplacedSpread, error.Code);
        Assert.Equal(new SourceSpan(line, column, endLine, endColumn), error.Span);
        Assert.Contains("on an earlier line continued as multiplication", error.Message, StringComparison.Ordinal);
        Assert.Contains("`A*,`", error.Message, StringComparison.Ordinal);

        var failure = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source));
        var reported = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.MisplacedSpread, reported.Code);
        Assert.Equal(error.Span, reported.Span);
    }

    [Fact]
    public void SameLineSpreadOperand_KeepsTheGenericMisplacedSpreadWording()
    {
        var error = Assert.Single(SourceProvenance.ExpectFrontEndError("A = 1, 2\nB = 3, 4\nA* B*"));
        Assert.Equal(DiagnosticCode.MisplacedSpread, error.Code);
        Assert.Equal(new SourceSpan(3, 4, 3, 6), error.Span);
        Assert.DoesNotContain("earlier line", error.Message, StringComparison.Ordinal);
        Assert.Contains("scalar operand", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ConsecutiveLineFinalStars_ChainAsMultiplication_UntilASpreadEndsTheChain()
    {
        // `A*` newline `B*` newline `C*`: the first two stars multiply; only the LAST, before the
        // end of input, is a spread — the misplaced operand — reported once, at `C*`.
        var error = Assert.Single(SourceProvenance.ExpectFrontEndError("A = 1, 2\nB = 3, 4\nC = 5, 6\nA*\nB*\nC*"));
        Assert.Equal(DiagnosticCode.MisplacedSpread, error.Code);
        Assert.Equal(new SourceSpan(6, 1, 6, 3), error.Span);
        Assert.Contains("on an earlier line continued as multiplication", error.Message, StringComparison.Ordinal);
    }
}
