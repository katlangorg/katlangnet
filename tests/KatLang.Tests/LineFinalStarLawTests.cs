using System.Globalization;
using System.Text.RegularExpressions;

namespace KatLang.Tests;

/// <summary>
/// THE LINE-FINAL STAR LAW (issue #183, owner decision 2026-10-14, refining Q-65): a <c>*</c>
/// that follows a completed expression and is the final significant token of its physical line —
/// across blank lines and comments, EOF included — is classified by ATTACHMENT. An attached
/// <c>A*</c> is the postfix spread marker and COMPLETES the expression, so the canonical newline
/// rule lets the next line begin an independent row or declaration (<c>A*</c> newline <c>B</c> is
/// two rows; <c>X = A*</c> newline <c>X</c> is the spread definition and the row <c>X</c>); a
/// detached <c>A *</c> is binary multiplication that leaves the expression INCOMPLETE, so it
/// continues across the newline with ordinary operator precedence (<c>A *</c> newline <c>B</c> is
/// <c>A * B</c>), and a following declaration head is never its operand. A star with a same-line
/// operand multiplies whatever its spacing. Neither layout carries a warning.
///
/// <para>History: Q-33 (2026-10-09) classified every line-final star like a same-line star
/// (multiplication before an operand), and the Q-65 revision of 2026-10-14 made every physical
/// line-final star multiplication, EOF included; #183 supersedes that subrule while keeping
/// Q-65's grammar-priority newline architecture. Every multiplication case those suites pinned
/// survives here in its detached spelling, beside its attached spread counterpart.</para>
///
/// <para>Valid-source cases require an empty diagnostic list at every severity; negative cases
/// assert the expected diagnostics instead. Values are observed on the six routes of
/// <see cref="SixRouteAgreement"/>. T1 compositional contexts × layouts for both roles, T2 the
/// spread endings and their detached missing-operand twins, T3 the canonical witness in both
/// spellings, T4 multiline multiplication and precedence, T5 identifier independence, T6 modules
/// and deferred branches, T7 the diagnostics of genuinely misplaced spreads. The compact acceptance
/// matrix is <see cref="LineFinalStarAttachmentTests"/>; also pinned by <c>StarSyntaxTests</c> and
/// the spec cases <c>star-before-*</c> and <c>line-final-star-*</c>.</para>
/// </summary>
public class LineFinalStarLawTests
{
    private const string ProductDefinitions = "A = 4\nB = 6\n";
    private const string SpreadDefinitions = "A = 1, 2\nB = 6\n";
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
        Expr.Index(var target, var selectors) => $"index({Shape(target)}, {Join(selectors)})",
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

    /// <summary>The declared names and the root rows, without rendering any property body.</summary>
    private static string NamesAndRows(Algorithm.User root)
        => $"names: {string.Join(", ", root.Properties.Select(p => p.Name))}; rows: {Rows(root)}";

    private static Algorithm Body(Algorithm owner, string name)
        => Assert.Single(owner.Properties, p => p.Name == name).Value;

    private static Algorithm DeconstructionSource(Algorithm.User root)
        => Assert.Single(root.Properties, p => p.Name.StartsWith("$deconstruct", StringComparison.Ordinal)).Value;

    private static SourceProvenance ParseWithoutAnyDiagnostic(string source)
    {
        var parsed = SourceProvenance.ParseValid(source);
        // Both layouts are valid source and carry NO diagnostic of any severity — no error,
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

    /// <summary>
    /// The product <c>A * B</c> in every spelling that multiplies: every same-line spacing, every
    /// DETACHED line-final star, and the leading star of a continuation line. The first is the
    /// reference.
    /// </summary>
    private static readonly Dictionary<string, string> ProductLayouts = new(StringComparer.Ordinal)
    {
        ["same line, detached"] = "A * B",
        ["same line, attached"] = "A* B",
        ["same line, attached both sides"] = "A*B",
        ["same line, attached to the operand"] = "A *B",
        ["LF, detached"] = "A *\nB",
        ["CRLF, detached"] = "A *\r\nB",
        ["tab before the star"] = "A\t*\nB",
        ["trailing spaces after the star"] = "A *   \nB",
        ["tab-indented operand"] = "A *\n\tB",
        ["space-indented operand"] = "A *\n        B",
        ["comment after the star"] = "A * # the operand follows\nB",
        ["blank lines"] = "A *\n\n\nB",
        ["comment-only line between"] = "A *\n# the operand follows\nB",
        ["CRLF, blank line, comment, tab"] = "A *\r\n\r\n# note\r\n\tB",
        ["detached, comment, blank line"] = "A * # note\n\nB",
        ["leading star"] = "A\n* B",
        ["leading star, attached to the operand"] = "A\n*B",
    };

    /// <summary>
    /// The spread row <c>A*</c> followed by the independent item <c>B</c>, in every layout that
    /// ends the line with an ATTACHED star. The first is the reference.
    /// </summary>
    private static readonly Dictionary<string, string> SpreadLayouts = new(StringComparer.Ordinal)
    {
        ["LF, attached"] = "A*\nB",
        ["CRLF, attached"] = "A*\r\nB",
        ["trailing spaces after the star"] = "A*   \nB",
        ["tab-indented item"] = "A*\n\tB",
        ["space-indented item"] = "A*\n        B",
        ["comment after the star"] = "A* # the spread ends here\nB",
        ["blank lines"] = "A*\n\n\nB",
        ["comment-only line between"] = "A*\n# the next item\nB",
        ["CRLF, blank line, comment, tab"] = "A*\r\n\r\n# note\r\n\tB",
    };

    private sealed record Context(string Template, Func<Algorithm.User, string> Locate, string ExpectedShape, string ExpectedValue);

    /// <summary>
    /// Where the product stands. <see cref="Context.Locate"/> renders the product's host AND the
    /// surrounding rows, so a continuation that swallowed or released the wrong line changes it.
    /// </summary>
    private static readonly Dictionary<string, Context> ProductContexts = new(StringComparer.Ordinal)
    {
        ["root row"] = new(
            ProductDefinitions + "{P}",
            static root => $"rows: {Rows(root)}",
            "rows: *(A, B)", "24"),
        ["definition body"] = new(
            ProductDefinitions + "X = {P}\nX",
            static root => $"X: {Rows(Body(root, "X"))}; rows: {Rows(root)}",
            "X: *(A, B); rows: X", "24"),
        ["clause branch body"] = new(
            ProductDefinitions + "F(0) = 0\nF(n) = {P}\nF(1)",
            static root => $"F: {AlgorithmShape(Body(root, "F"))}; rows: {Rows(root)}",
            "F: family[0 / *(A, B)]; rows: call(F; 1)", "24"),
        ["deconstruction right-hand side"] = new(
            ProductDefinitions + "x, y = {P}, 1\nx",
            static root => $"rhs: {Rows(DeconstructionSource(root))}; rows: {Rows(root)}",
            "rhs: *(A, B) | 1; rows: x", "24"),
        ["brace block row"] = new(
            ProductDefinitions + "{ {P} }",
            static root => $"rows: {Rows(root)}",
            "rows: block(*(A, B))", "24"),
        ["brace definition body"] = new(
            ProductDefinitions + "X = {\n  {P}\n}\nX",
            static root => $"X: {Rows(Body(root, "X"))}; rows: {Rows(root)}",
            "X: *(A, B); rows: X", "24"),
        ["parenthesized operand"] = new(
            ProductDefinitions + "1 + ({P})",
            static root => $"rows: {Rows(root)}",
            "rows: +(1, *(A, B))", "25"),
        ["list element"] = new(
            ProductDefinitions + "[{P}]",
            static root => $"rows: {Rows(root)}",
            "rows: list(*(A, B))", "L[24]"),
        ["argument"] = new(
            ProductDefinitions + "F(x) = x\nF({P})",
            static root => $"rows: {Rows(root)}",
            "rows: call(F; *(A, B))", "24"),
        ["first of two arguments"] = new(
            ProductDefinitions + "G(x, y) = x - y\nG({P}, 1)",
            static root => $"rows: {Rows(root)}",
            "rows: call(G; *(A, B), 1)", "23"),
        ["selector"] = new(
            ProductDefinitions + "L = [100, 101]\nL[{P} - 23]",
            static root => $"rows: {Rows(root)}",
            "rows: index(L, -(*(A, B), 23))", "101"),
        ["callback body"] = new(
            ProductDefinitions + "map([1, 2], { {P} + x })",
            static root => $"rows: {Rows(root)}",
            "rows: call(map; list(1, 2), block(+(*(A, B), $x)))", "L[25, 26]"),
        ["inline module member"] = new(
            "M = { public A = 4\n  public B = 6\n  public X = {P}\n  0 }\nM.X",
            static root => $"M.X: {Rows(Body(Body(root, "M"), "X"))}; M rows: {Rows(Body(root, "M"))}; rows: {Rows(root)}",
            "M.X: *(A, B); M rows: 0; rows: dot(M.X)", "24"),
    };

    /// <summary>
    /// Where the spread row stands. The spread supplies two items (<c>A = 1, 2</c>) and <c>B</c> one,
    /// so every expected cardinality is independent of the product contexts above: in a
    /// line-bounded body the attached spread ends the body and <c>B</c> becomes the enclosing
    /// scope's next row, in an expression list it becomes the next slot.
    /// </summary>
    private static readonly Dictionary<string, Context> SpreadContexts = new(StringComparer.Ordinal)
    {
        ["root row"] = new(
            SpreadDefinitions + "{P}",
            static root => $"rows: {Rows(root)}",
            "rows: spread(A) | B", "S[1, 2, 6]"),
        ["definition body"] = new(
            SpreadDefinitions + "X = {P}\nX",
            static root => $"X: {Rows(Body(root, "X"))}; rows: {Rows(root)}",
            "X: spread(A); rows: B | X", "S[6, S[1, 2]]"),
        ["clause branch body"] = new(
            SpreadDefinitions + "F(0) = 0\nF(n) = {P}\nF(1)",
            static root => $"F: {AlgorithmShape(Body(root, "F"))}; rows: {Rows(root)}",
            "F: family[0 / spread(A)]; rows: B | call(F; 1)", "S[6, S[1, 2]]"),
        ["deconstruction right-hand side"] = new(
            SpreadDefinitions + "x, y = {P}\nx + y",
            static root => $"rhs: {Rows(DeconstructionSource(root))}; rows: {Rows(root)}",
            "rhs: spread(A); rows: B | +(x, y)", "S[6, 3]"),
        ["brace block row"] = new(
            SpreadDefinitions + "{ {P} }",
            static root => $"rows: {Rows(root)}",
            "rows: block(spread(A) | B)", "S[1, 2, 6]"),
        ["brace definition body"] = new(
            SpreadDefinitions + "X = {\n  {P}\n}\nX",
            static root => $"X: {Rows(Body(root, "X"))}; rows: {Rows(root)}",
            "X: spread(A) | B; rows: X", "S[1, 2, 6]"),
        ["parenthesized capture"] = new(
            SpreadDefinitions + "count(({P}))",
            static root => $"rows: {Rows(root)}",
            "rows: call(count; capture(spread(A), B))", "3"),
        ["list element"] = new(
            SpreadDefinitions + "[{P}]",
            static root => $"rows: {Rows(root)}",
            "rows: list(spread(A), B)", "L[1, 2, 6]"),
        ["argument"] = new(
            SpreadDefinitions + "Coll(*xs) = xs\nColl({P})",
            static root => $"rows: {Rows(root)}",
            "rows: call(Coll; spread(A), B)", "L[1, 2, 6]"),
        ["selector"] = new(
            SpreadDefinitions + "L = [10, 20, 30, 40, 50, 60, 70]\nL[{P}]",
            static root => $"rows: {Rows(root)}",
            "rows: index(L, spread(A), B)", "S[20, 30, 70]"),
        ["callback body"] = new(
            SpreadDefinitions + "map([1, 2], { {P} + x })",
            static root => $"rows: {Rows(root)}",
            "rows: call(map; list(1, 2), block(spread(A) | +(B, $x)))", "L[S[1, 2, 7], S[1, 2, 8]]"),
        ["inline module member"] = new(
            "M = { public A = 1, 2\n  public B = 6\n  public X = {P}\n  0 }\nM.X",
            static root => $"M.X: {Rows(Body(Body(root, "M"), "X"))}; M rows: {Rows(Body(root, "M"))}; rows: {Rows(root)}",
            "M.X: spread(A); M rows: B | 0; rows: dot(M.X)", "S[1, 2]"),
    };

    public static TheoryData<string, string> ProductContextsByLayout() => Cross(ProductContexts.Keys, ProductLayouts.Keys);

    public static TheoryData<string, string> SpreadContextsByLayout() => Cross(SpreadContexts.Keys, SpreadLayouts.Keys);

    private static TheoryData<string, string> Cross(IEnumerable<string> contexts, IEnumerable<string> layouts)
    {
        var data = new TheoryData<string, string>();
        foreach (var context in contexts)
        {
            foreach (var layout in layouts)
                data.Add(context, layout);
        }

        return data;
    }

    private static string ProductProgram(string context, string layout)
        => ProductContexts[context].Template.Replace("{P}", ProductLayouts[layout], StringComparison.Ordinal);

    private static string SpreadProgram(string context, string layout)
        => SpreadContexts[context].Template.Replace("{P}", SpreadLayouts[layout], StringComparison.Ordinal);

    [Theory]
    [MemberData(nameof(ProductContextsByLayout))]
    public async Task DetachedOrSameLineStar_IsMultiplication_InEveryContextAndLayout(string context, string layout)
    {
        var source = ProductProgram(context, layout);
        var parsed = ParseWithoutAnyDiagnostic(source);

        // The product is ONE multiplication node whose right operand is exactly `B`, and every
        // surrounding row and declaration stays where it was written.
        Assert.Equal(ProductContexts[context].ExpectedShape, ProductContexts[context].Locate(parsed.Root));

        // Layout independence: the elaborated program is the very program of the one-line
        // `A * B` spelling (the encoder is span-free), and so is its value on every route.
        var reference = SourceProvenance.ParseValid(ProductProgram(context, "same line, detached"));
        Assert.Equal(LeanAstEncoder.EncodeProgram(reference.Root), LeanAstEncoder.EncodeProgram(parsed.Root));
        Assert.Equal(ProductContexts[context].ExpectedValue, await ValueOnEveryRoute(source));
    }

    [Theory]
    [MemberData(nameof(SpreadContextsByLayout))]
    public async Task AttachedLineFinalStar_IsACompletedSpread_InEveryContextAndLayout(string context, string layout)
    {
        var source = SpreadProgram(context, layout);
        var parsed = ParseWithoutAnyDiagnostic(source);

        // The spread is ONE completed slot, and `B` is the next row or slot of the construct that
        // owns the line — never a multiplication operand.
        Assert.Equal(SpreadContexts[context].ExpectedShape, SpreadContexts[context].Locate(parsed.Root));

        // Layout independence among the attached spellings: comments, blank lines, indentation
        // and CRLF neither manufacture nor destroy the completed spread.
        var reference = SourceProvenance.ParseValid(SpreadProgram(context, "LF, attached"));
        Assert.Equal(LeanAstEncoder.EncodeProgram(reference.Root), LeanAstEncoder.EncodeProgram(parsed.Root));
        Assert.Equal(SpreadContexts[context].ExpectedValue, await ValueOnEveryRoute(source));
    }

    // ── T2: the spread endings, and their detached twins ─────────────────────

    public static TheoryData<string, string, string> SpreadEndings() => new()
    {
        // A comma ends the spread slot; the next line is a row of its own.
        { "A = (1, 2)\nB = 5\nA*,\nB", "names: A, B; rows: spread(A) | B", "S[1, 2, 5]" },
        { "A = (1, 2)\nB = 5\nA*, # end of the spread row\r\nB", "names: A, B; rows: spread(A) | B", "S[1, 2, 5]" },
        // A leading comma continues the completed spread's expression list backward.
        { "A = (1, 2)\nB = 5\nA*\n, B", "names: A, B; rows: spread(A) | B", "S[1, 2, 5]" },
        // The end of the physical line ends an attached spread, in a definition body too.
        { "A = (1, 2)\nB = 5\nA*\nB", "names: A, B; rows: spread(A) | B", "S[1, 2, 5]" },
        { "A = (1, 2)\nB = 5\nX = A*\nB\nX", "names: A, B, X; rows: B | X", "S[5, S[1, 2]]" },
        // Structural closing of a spread-ending definition body is still available.
        { "A = (1, 2)\nB = 5\nX = (A*)\nB\nX", "names: A, B, X; rows: B | X", "S[5, S[1, 2]]" },
        { "A = (1, 2)\nB = 5\nX = { A* }\nB\nX", "names: A, B, X; rows: B | X", "S[5, S[1, 2]]" },
        // A following declaration head begins its own declaration after the completed spread.
        { "A = (1, 2)\nA*\nB = 5\nB", "names: A, B; rows: spread(A) | B", "S[1, 2, 5]" },
        { "A = (1, 2)\nA*\npublic B = 5\nB", "names: A, B; rows: spread(A) | B", "S[1, 2, 5]" },
        { "A = (1, 2)\nA*\nF(x) = x + 3\nF(2)", "names: A, F; rows: spread(A) | call(F; 2)", "S[1, 2, 5]" },
        { "A = (1, 2)\nA*\nx, y = 4, 5\ny", "names: A, $deconstruct$0, x, y; rows: spread(A) | y", "S[1, 2, 5]" },
        { "A = (1, 2)\nA*\n*items = 4, 5\nitems[1]", "names: A, $deconstruct$0, items; rows: spread(A) | index(items, 1)", "S[1, 2, 5]" },
        { "A = (1, 2)\nX = A*\nY = 5\nX, Y", "names: A, X, Y; rows: X | Y", "S[S[1, 2], 5]" },
        { "A = (1, 2)\n{ A*\n  Y = 5\n  Y }", "names: A; rows: block({Y = 5} spread(A) | Y)", "S[1, 2, 5]" },
        // A later-line closing delimiter or the end of input stays with its owner.
        { "A = (1, 2)\n(A*\n)", "names: A; rows: capture(spread(A))", "S[1, 2]" },
        { "A = (1, 2)\n[A*\n]", "names: A; rows: list(spread(A))", "L[1, 2]" },
        { "A = (1, 2)\n{ A*\n}", "names: A; rows: block(spread(A))", "S[1, 2]" },
        { "Coll(*xs) = xs\nA = (1, 2)\nColl(A*\n)", "names: A, Coll; rows: call(Coll; spread(A))", "L[1, 2]" },
        { "A = (1, 2)\nA*", "names: A; rows: spread(A)", "S[1, 2]" },
        { "A = (1, 2)\nA* # the end\n\n# nothing follows", "names: A; rows: spread(A)", "S[1, 2]" },
        { "A = (1, 2)\nX\nX = A*", "names: A, X; rows: X", "S[1, 2]" },
        // Tokens that cannot continue the completed spread begin their own row.
        { "A = (1, 2)\nA*\nnot true", "names: A; rows: spread(A) | not(true)", "S[1, 2, false]" },
        // A leading dot continues it as a fluent spread receiver.
        { "Coll(*xs) = xs\nA = (1, 2)\nA*\n.Coll", "names: A, Coll; rows: call(Coll; spread(A))", "L[1, 2]" },
    };

    [Theory]
    [MemberData(nameof(SpreadEndings))]
    public async Task SpreadEnding_ProducesTheSpreadNode_AndKeepsTheNextRowSeparate(string source, string expectedProgram, string expectedValue)
    {
        var parsed = ParseWithoutAnyDiagnostic(source);
        Assert.Equal(expectedProgram, NamesAndRows(parsed.Root));
        var scan = new RejectedStarShape();
        scan.VisitAlgorithm(parsed.Root);
        Assert.Empty(scan.Products);
        Assert.Equal(expectedValue, await ValueOnEveryRoute(source));
    }

    /// <summary>
    /// The DETACHED twin of every boundary above that is not itself an operand: the star is
    /// multiplication, nothing it may take follows, and the incomplete multiplication is the one
    /// error — a following declaration head stays a declaration, a closer stays with its owner.
    /// </summary>
    public static TheoryData<string> DetachedStarBeforeABoundary() => new()
    {
        "A = (1, 2)\nA *\nB = 5\nB",
        "A = (1, 2)\nA *\npublic B = 5\nB",
        "A = (1, 2)\nA *\nF(x) = x + 3\nF(2)",
        "A = (1, 2)\nA *\nx, y = 4, 5\ny",
        "A = (1, 2)\nA *\n*items = 4, 5\nitems[1]",
        "A = (1, 2)\nX = A *\nY = 5\nX, Y",
        "A = (1, 2)\n{ A *\n  Y = 5\n  Y }",
        "A = (1, 2)\n(A *\n)",
        "A = (1, 2)\n[A *\n]",
        "A = (1, 2)\n{ A *\n}",
        "Coll(*xs) = xs\nA = (1, 2)\nColl(A *\n)",
        "A = (1, 2)\nA *",
        "A = (1, 2)\nA * # the end\n\n# nothing follows",
        "A = (1, 2)\nX\nX = A *",
        "A = (1, 2)\nA *\nnot true",
        "Coll(*xs) = xs\nA = (1, 2)\nA *\n.Coll",
    };

    [Theory]
    [MemberData(nameof(DetachedStarBeforeABoundary))]
    public void DetachedLineFinalStar_BeforeABoundary_IsTheIncompleteMultiplication(string source)
    {
        var rejected = Parser.ParseSyntax(source);
        Assert.True(rejected.HasErrors);
        Assert.Contains(rejected.Diagnostics, d => d.Code == DiagnosticCode.UnexpectedToken);
        var scan = new RejectedStarShape();
        scan.VisitAlgorithm(rejected.Root);
        var product = Assert.Single(scan.Products);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(product.Left).Name);
        Assert.Empty(scan.Spreads);
        Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source));
    }

    [Fact]
    public async Task TrailingCommaInADefinitionBody_ContinuesTheBody_SoItEndsASlotButNotABody()
    {
        // The comma ends the spread SLOT, but a trailing comma continues the line-bounded body, so
        // the next row becomes the body's next slot. Without the comma, the end of the line ends
        // the body after an attached spread (T2 above).
        const string source = "A = (1, 2)\nX = A*,\n3\nX";
        var parsed = ParseWithoutAnyDiagnostic(source);
        Assert.Equal("{A = capture(1, 2); X = spread(A) | 3} X", ProgramShape(parsed.Root));
        Assert.Equal("S[1, 2, 3]", await ValueOnEveryRoute(source));
    }

    // ── T3: the canonical witness, in both spellings ─────────────────────────

    [Fact]
    public async Task CanonicalWitness_AttachedStar_EndsTheDefinition_AndKeepsTheRow()
    {
        const string source = "A = 2\nX = A*\nX";
        var parsed = ParseWithoutAnyDiagnostic(source);

        // The attached star completes `X = A*`; the next line is the root row `X`.
        Assert.Equal("spread(A)", Rows(Body(parsed.Root, "X")));
        Assert.Equal("X", Rows(parsed.Root));
        Assert.Equal("2", await ValueOnEveryRoute(source));
    }

    [Fact]
    public async Task CanonicalWitness_DetachedStar_ContinuesTheDefinition_LeavesNoOutputRow_AndReportsNothing()
    {
        const string source = "A = 2\nX = A *\nX";
        var parsed = ParseWithoutAnyDiagnostic(source);

        // X = A * X: the detached star leaves the definition incomplete, `X` begins an operand
        // and no declaration, so the definition continues across the newline; no root row remains.
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
    public async Task CanonicalWitness_WithANumberRow_IsTwoRowsAttached_AndOneProductDetached()
    {
        const string attached = "A = 2\nX = A*\n3\nX";
        var spread = ParseWithoutAnyDiagnostic(attached);
        Assert.Equal("spread(A)", Rows(Body(spread.Root, "X")));
        Assert.Equal("3 | X", Rows(spread.Root));
        Assert.Equal("S[3, 2]", await ValueOnEveryRoute(attached));

        const string detached = "A = 2\nX = A *\n3\nX";
        var product = ParseWithoutAnyDiagnostic(detached);
        Assert.Equal("*(A, 3)", Rows(Body(product.Root, "X")));
        Assert.Equal("X", Rows(product.Root));
        Assert.Equal("6", await ValueOnEveryRoute(detached));
    }

    // ── T4: multiline multiplication keeps ordinary precedence ───────────────

    public static TheoryData<string, string, string> MultilineProducts() => new()
    {
        { "A = 4\nB = 6\nA *\n(B + 1)", "*(A, +(B, 1))", "28" },
        { "A = 4\nB = 6\nA\n* (B + 1)", "*(A, +(B, 1))", "28" },
        // The continuation is token-level: the next line is NOT one operand.
        { "A = 4\nB = 6\nA *\nB + 1", "+(*(A, B), 1)", "25" },
        { "A = 4\nB = 6\nA *\nB - 1", "-(*(A, B), 1)", "23" },
        { "A = 4\nB = 6\nA *\nB ^ 2", "*(A, ^(B, 2))", "144" },
        { "A = 4\nB = 6\nA *\n-B", "*(A, neg(B))", "-24" },
        { "A = 4\nL = [6]\nA *\nL[0]", "*(A, index(L, 0))", "24" },
        { "A = 4\nB = 6\nA *\nB == 24", "cmp(*(A, B) == 24)", "true" },
        { "A = 4\nB = 6\nC = 2\nA *\nB *\nC", "*(*(A, B), C)", "48" },
        { "map([1, 2], { x *\n  (x + 1) })", "call(map; list(1, 2), block(*($x, +($x, 1))))", "L[2, 6]" },
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

    /// <summary>
    /// The attached twins of <see cref="MultilineProducts"/>: the completed spread ends its row and
    /// the next line is an independent expression with its own ordinary precedence.
    /// </summary>
    public static TheoryData<string, string, string> AttachedSpreadRowsBeforeExpressions() => new()
    {
        { "A = 4\nB = 6\nA*\n(B + 1)", "spread(A) | +(B, 1)", "S[4, 7]" },
        { "A = 4\nB = 6\nA*\nB + 1", "spread(A) | +(B, 1)", "S[4, 7]" },
        { "A = 4\nB = 6\nA*\nB ^ 2", "spread(A) | ^(B, 2)", "S[4, 36]" },
        { "A = 4\nB = 6\nA*\n-B", "spread(A) | neg(B)", "S[4, -6]" },
        { "A = 4\nL = [6]\nA*\nL[0]", "spread(A) | index(L, 0)", "S[4, 6]" },
        { "A = 4\nB = 6\nA*\nB == 24", "spread(A) | cmp(B == 24)", "S[4, false]" },
        { "A = 4\nB = 6\nC = 2\nA*\nB*\nC", "spread(A) | spread(B) | C", "S[4, 6, 2]" },
        { "map([1, 2], { x*\n  (x + 1) })", "call(map; list(1, 2), block(spread($x) | +($x, 1)))", "L[S[1, 2], S[2, 3]]" },
    };

    [Theory]
    [MemberData(nameof(AttachedSpreadRowsBeforeExpressions))]
    public async Task AttachedSpread_EndsItsRow_AndTheNextLineKeepsOrdinaryPrecedence(string source, string expectedRows, string expectedValue)
    {
        var parsed = ParseWithoutAnyDiagnostic(source);
        Assert.Equal(expectedRows, Rows(parsed.Root));
        Assert.Equal(expectedValue, await ValueOnEveryRoute(source));
    }

    public static TheoryData<string, string, string, string> MultilineDefinitionBodies() => new()
    {
        { "A = 2\nB = 3\nX = A *\nB + 1\nX", "X", "+(*(A, B), 1)", "7" },
        // The deconstruction RHS is `(V * x) + y`, never `V * (x + y)`: precedence is unchanged.
        { "V = [(1, 2)]\nx, y = V *\nx + y\nV", "$deconstruct$0", "+(*(V, x), y)", "L[S[1, 2]]" },
        { "P = {\n  A = 2\n  A *\n  3\n}\nP", "P", "*(A, 3)", "6" },
        { "Area(w, h) = w *\n  h\nArea(3, 4)", "Area", "*($w, $h)", "12" },
        { "Total = Price *\n  Qty\nPrice = 4\nQty = 3\nTotal", "Total", "*(Price, Qty)", "12" },
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

    public static TheoryData<string, string, string, string, string> AttachedSpreadDefinitionBodies() => new()
    {
        { "A = 2\nB = 3\nX = A*\nB + 1\nX", "X", "spread(A)", "+(B, 1) | X", "S[4, 2]" },
        // The unpacking receiver opens the one spread item `(1, 2)`; the next line is a row.
        { "V = [(1, 2)]\nx, y = V*\nx + y\nV", "$deconstruct$0", "spread(V)", "+(x, y) | V", "S[3, L[S[1, 2]]]" },
        { "P = {\n  A = 2\n  A*\n  3\n}\nP", "P", "spread(A) | 3", "P", "S[2, 3]" },
        { "Total = Price*\n  Qty\nPrice = 4\nQty = 3\nTotal", "Total", "spread(Price)", "Qty | Total", "S[3, 4]" },
    };

    [Theory]
    [MemberData(nameof(AttachedSpreadDefinitionBodies))]
    public async Task AttachedSpread_EndsALineBoundedDefinitionBody(
        string source, string property, string expectedBody, string expectedRows, string expectedValue)
    {
        var parsed = ParseWithoutAnyDiagnostic(source);
        Assert.Equal(expectedBody, Rows(Body(parsed.Root, property)));
        Assert.Equal(expectedRows, Rows(parsed.Root));
        Assert.Equal(expectedValue, await ValueOnEveryRoute(source));
    }

    [Fact]
    public void AttachedSpread_EndingAParameterizedBody_LeavesTheNextLineToTheRoot()
    {
        // `Area(w, h) = w*` is complete: `h` on the next line is a ROOT row, where nothing declares
        // it — the ordinary unresolved-root-name error, never a silent product with the parameter.
        const string source = "Area(w, h) = w*\n  h\nArea(3, 4)";
        var parsed = ParseWithoutAnyDiagnostic(source);
        Assert.Equal("spread($w)", Rows(Body(parsed.Root, "Area")));
        Assert.Equal("$h | call(Area; 3, 4)", Rows(parsed.Root));
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
        Assert.Equal(KatLangErrorCode.UnresolvedImplicitParams, Assert.Single(failure.Errors).Code);
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

    private sealed class RejectedStarShape : AstWalker
    {
        public List<Expr.Binary> Products { get; } = [];
        public List<Expr.SequenceSpread> Spreads { get; } = [];
        public override void VisitExpr(Expr expr)
        {
            if (expr is Expr.Binary { Op: BinaryOp.Mul } p) Products.Add(p);
            if (expr is Expr.SequenceSpread spread) Spreads.Add(spread);
            base.VisitExpr(expr);
        }
    }

    private static string Rename(string text)
    {
        foreach (var (from, to) in Renaming)
            text = Regex.Replace(text, $@"\b{from}\b", to, RegexOptions.CultureInvariant);
        return text;
    }

    public static TheoryData<string> RenamablePrograms()
    {
        var data = new TheoryData<string>();
        foreach (var context in ProductContexts.Keys)
        {
            data.Add(ProductProgram(context, "LF, detached"));
            data.Add(ProductProgram(context, "CRLF, blank line, comment, tab"));
        }

        foreach (var context in SpreadContexts.Keys)
        {
            data.Add(SpreadProgram(context, "LF, attached"));
            data.Add(SpreadProgram(context, "CRLF, blank line, comment, tab"));
        }

        foreach (var star in new[] { "*", " *" })
        {
            data.Add($"A = 2\nX = A{star}\nX\n7");
            data.Add($"A = 2\nX = A{star}\n3\nX");
            data.Add($"A = 2\nY = 5\nX = A{star}\nY\nX");
            data.Add($"A = 2\nY = 5\nX = A{star}\nX\nY");
            data.Add($"A = 2\nB = 3\nX = A{star}\nB + 1\nX");
            data.Add($"V = [(1, 2)]\nx, y = V{star}\nx + y\nV");
        }

        data.Add("A = (1, 2)\nB = 5\nX = (A*)\nB\nX");
        data.Add("A = (1, 2)\nA*, 0\nB = 5\nB");
        data.Add("A = (1, 2)\nX = { A* }\nY = 5\nX, Y");
        return data;
    }

    [Theory]
    [MemberData(nameof(RenamablePrograms))]
    public async Task Renaming_NeverChangesTheClassification(string source)
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
    public void NextLineName_NamingTheDefinitionItself_OrAnotherName_IsClassifiedAlike()
    {
        // Detached: the name is the multiplication operand, whichever name it is.
        Assert.Equal("*(A, X)", Rows(Body(ParseWithoutAnyDiagnostic("A = 2\nY = 5\nX = A *\nX\nY").Root, "X")));
        Assert.Equal("*(A, Y)", Rows(Body(ParseWithoutAnyDiagnostic("A = 2\nY = 5\nX = A *\nY\nX").Root, "X")));

        // Attached: the name is the next root row, whichever name it is.
        var self = ParseWithoutAnyDiagnostic("A = 2\nY = 5\nX = A*\nX\nY").Root;
        Assert.Equal("spread(A)", Rows(Body(self, "X")));
        Assert.Equal("X | Y", Rows(self));
        var other = ParseWithoutAnyDiagnostic("A = 2\nY = 5\nX = A*\nY\nX").Root;
        Assert.Equal("spread(A)", Rows(Body(other, "X")));
        Assert.Equal("Y | X", Rows(other));
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
    [InlineData("public A = 2\npublic X = A *\nY\npublic Y = 3\n0", "*(A, Y)", "0", "6")]
    [InlineData("public A = 2\r\npublic X = A *\r\nY\r\npublic Y = 3\r\n0", "*(A, Y)", "0", "6")]
    [InlineData("public A = 2\npublic X = A *\n\n# continued\n  Y\npublic Y = 3\n0\n", "*(A, Y)", "0", "6")]
    [InlineData("public A = 2\npublic X = A*\nY\npublic Y = 3\n0", "spread(A)", "Y | 0", "2")]
    [InlineData("public A = 2\r\npublic X = A*\r\nY\r\npublic Y = 3\r\n0", "spread(A)", "Y | 0", "2")]
    [InlineData("public A = 2\npublic X = A*\n\n# a row\n  Y\npublic Y = 3\n0\n", "spread(A)", "Y | 0", "2")]
    public async Task LoadedModuleText_FollowsTheSameLaw(string module, string memberBody, string moduleRows, string value)
    {
        var modules = new CountingModules([(Lib, module)]);
        var parsed = await ParseModuleProgramWithoutAnyDiagnostic($"open '{Lib}'\nX", modules.Options);
        var opened = OpenedModule(parsed.Root);
        Assert.Equal(memberBody, Rows(Body(opened, "X")));
        Assert.Equal(moduleRows, Rows(opened));
        Assert.Equal(value, await RunAsyncValue($"open '{Lib}'\nX", new CountingModules([(Lib, module)]).Options));
    }

    [Theory]
    [InlineData("public A = (1, 2)\npublic X = A *")]
    [InlineData("public A = (1, 2)\npublic X = A *\n")]
    [InlineData("public A = (1, 2)\r\npublic X = A *\r\n\r\n# the end of the module\r\n")]
    public async Task ModuleSourceEndingInADetachedStar_RejectsAtItsOwnEofWithoutTakingLoadSiteOperands(string module)
    {
        Assert.True(Parser.ParseSyntax(module).HasErrors);
        const string source = $"M = load('{Lib}')\nM.X\n5";
        var result = await KatLangEngine.RunAsync(source, new CountingModules([(Lib, module)]).Options);
        Assert.IsType<RunResult.ParseFailure>(result);
    }

    [Theory]
    [InlineData("public A = (1, 2)\npublic X = A*")]
    [InlineData("public A = (1, 2)\npublic X = A*\n")]
    [InlineData("public A = (1, 2)\r\npublic X = A*\r\n\r\n# the end of the module\r\n")]
    public async Task ModuleSourceEndingInAnAttachedStar_EndsItsLastMemberWithASpread(string module)
    {
        Assert.Empty(Parser.ParseSyntax(module).Diagnostics.ToArray());
        const string source = $"M = load('{Lib}')\nM.X\n5";
        Assert.Equal("S[S[1, 2], 5]", await RunAsyncValue(source, new CountingModules([(Lib, module)]).Options));
    }

    [Fact]
    public async Task SpreadRowInModuleText_EndsAtTheLineAttached_AndMultipliesDetached()
    {
        // The attached spelling is the ModuleCoordinateSpaceTests fixture's shape: the spread row and
        // the selection row are two rows with or without a trailing comma. Only a DETACHED star
        // continues into the next line as multiplication.
        const string attached = "open Math\npublic F(x, (y, *z)) = x + y\npublic G(0) = 'a'\npublic G(n) = n.count\nH = { a, *b = 1, 2, 3\n a + b.count }\nF(1, (2, 3))*\n[H][0]";
        var separated = attached.Replace("F(1, (2, 3))*\n", "F(1, (2, 3))*,\n", StringComparison.Ordinal);
        var detached = attached.Replace("F(1, (2, 3))*\n", "F(1, (2, 3)) *\n", StringComparison.Ordinal);
        Assert.NotEqual(attached, separated);
        Assert.NotEqual(attached, detached);

        foreach (var twoRows in new[] { attached, separated })
        {
            var two = await ParseModuleProgramWithoutAnyDiagnostic($"M = load('{Lib}')\n1", new CountingModules([(Lib, twoRows)]).Options);
            Assert.Equal("spread(call(F; 1, capture(2, 3))) | index(list(H), 0)", Rows(Body(two.Root, "M")));
        }

        var one = await ParseModuleProgramWithoutAnyDiagnostic($"M = load('{Lib}')\n1", new CountingModules([(Lib, detached)]).Options);
        Assert.Equal("*(call(F; 1, capture(2, 3)), index(list(H), 0))", Rows(Body(one.Root, "M")));
    }

    [Theory]
    [InlineData(" *", "n", "*(V, 2)", "42", "5")]
    // Attached, the branch has two rows, so its sibling branch is written with two as well (the
    // clause-family output-arity rule).
    [InlineData("*", "n, 2", "spread(V) | 2", "S[21, 2]", "S[5, 2]")]
    public async Task DeferredBranch_IsParsedEagerly_UnderTheSameLaw_SelectedOrNot(
        string star, string siblingBody, string branchRows, string selectedValue, string unselectedValue)
    {
        const string module = "public V = 21\n0";
        var branches = $"F(0) = {{ open '{Lib}'\n  V{star}\n  2 }}\nF(n) = {siblingBody}\n";

        foreach (var row in new[] { "F(0)", "F(5)" })
        {
            // The load-bearing branch is parsed eagerly with the document: its body is classified
            // whether or not evaluation ever selects it.
            var raw = SourceProvenance.ParseSyntaxValidRoot(branches + row);
            var family = Assert.IsType<Algorithm.Conditional>(Body(raw, "F"));
            Assert.Equal(branchRows, Rows(family.Branches[0].Body));
            await ParseModuleProgramWithoutAnyDiagnostic(branches + row, new CountingModules([(Lib, module)]).Options);
        }

        // Selected: the deferred unit materializes.
        var selected = new CountingModules([(Lib, module)]);
        Assert.Equal(selectedValue, await RunAsyncValue(branches + "F(0)", selected.Options));
        Assert.Equal(1, selected.Fetches.GetValueOrDefault(Lib));

        // Never selected: never fetched, and the program runs.
        var unselected = new CountingModules([(Lib, module)]);
        Assert.Equal(unselectedValue, await RunAsyncValue(branches + "F(5)", unselected.Options));
        Assert.Equal(0, unselected.Fetches.GetValueOrDefault(Lib));
    }

    // ── T7: genuinely misplaced spreads keep their diagnostics ───────────────

    /// <summary>
    /// <c>A *</c> newline <c>B*</c>: the detached first star multiplies (an operand follows), so the
    /// spread <c>B*</c> becomes its right operand — the existing <c>MisplacedSpread</c>, reported
    /// at that spread with the targeted line-final explanation (F13a), in every context.
    /// </summary>
    public static TheoryData<string, int, int, int, int> SpreadOperandOnALaterLine() => new()
    {
        { "A = 1, 2\nB = 3, 4\nA *\nB*", 4, 1, 4, 3 },
        { "A = 1, 2\nB = 3, 4\nA *\r\nB*", 4, 1, 4, 3 },
        { "A = 1, 2\nB = 3, 4\nA * # note\n\n# more\nB*", 6, 1, 6, 3 },
        { "A = 1, 2\nB = 3, 4\nX = A *\nB*\nY = 5\nX", 4, 1, 4, 3 },
        { "A = 1, 2\nB = 3, 4\n{ A *\n  B* }", 4, 3, 4, 5 },
        { "A = 1, 2\nB = 3, 4\nF(x) = x\nF(A *\n  B*)", 5, 3, 5, 5 },
        { "A = 1, 2\nB = 3, 4\n[A *\nB*]", 4, 1, 4, 3 },
    };

    [Theory]
    [MemberData(nameof(SpreadOperandOnALaterLine))]
    public void SpreadOperandOnALaterLine_KeepsTheTargetedMisplacedSpreadDiagnostic(
        string source, int line, int column, int endLine, int endColumn)
    {
        var error = Assert.Single(SourceProvenance.ExpectFrontEndError(CloseLastSpread(source)));
        Assert.Equal(DiagnosticSeverity.Error, error.Severity);
        Assert.Equal(DiagnosticCode.MisplacedSpread, error.Code);
        Assert.Equal(new SourceSpan(line, column, endLine, endColumn), error.Span);
        Assert.Contains("is separated from its left operand", error.Message, StringComparison.Ordinal);
        Assert.Contains("attach the marker to its operand (`A*`)", error.Message, StringComparison.Ordinal);

        var failure = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(CloseLastSpread(source)));
        var reported = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.MisplacedSpread, reported.Code);
        Assert.Equal(error.Span, reported.Span);
    }

    /// <summary>The attached twins of <see cref="SpreadOperandOnALaterLine"/>: separate spread items.</summary>
    public static TheoryData<string, string, string> SpreadItemsOnConsecutiveLines() => new()
    {
        { "A = 1, 2\nB = 3, 4\nA*\nB*", "spread(A) | spread(B)", "S[1, 2, 3, 4]" },
        { "A = 1, 2\nB = 3, 4\nA*\r\nB*", "spread(A) | spread(B)", "S[1, 2, 3, 4]" },
        { "A = 1, 2\nB = 3, 4\nA* # note\n\n# more\nB*", "spread(A) | spread(B)", "S[1, 2, 3, 4]" },
        { "A = 1, 2\nB = 3, 4\nX = A*\nB*\nY = 5\nX", "spread(B) | X", "S[3, 4, S[1, 2]]" },
        { "A = 1, 2\nB = 3, 4\n{ A*\n  B* }", "block(spread(A) | spread(B))", "S[1, 2, 3, 4]" },
        { "A = 1, 2\nB = 3, 4\nF(*x) = x\nF(A*\n  B*)", "call(F; spread(A), spread(B))", "L[1, 2, 3, 4]" },
        { "A = 1, 2\nB = 3, 4\n[A*\nB*]", "list(spread(A), spread(B))", "L[1, 2, 3, 4]" },
    };

    [Theory]
    [MemberData(nameof(SpreadItemsOnConsecutiveLines))]
    public async Task AttachedSpreadsOnConsecutiveLines_AreSeparateItems(string source, string expectedRows, string expectedValue)
    {
        var parsed = ParseWithoutAnyDiagnostic(source);
        Assert.Equal(expectedRows, Rows(parsed.Root));
        Assert.Equal(expectedValue, await ValueOnEveryRoute(source));
    }

    [Fact]
    public void SameLineSpreadOperand_KeepsTheGenericMisplacedSpreadWording()
    {
        var error = Assert.Single(SourceProvenance.ExpectFrontEndError("A = 1, 2\nB = 3, 4\nA* B*, 0"));
        Assert.Equal(DiagnosticCode.MisplacedSpread, error.Code);
        Assert.Equal(new SourceSpan(3, 4, 3, 6), error.Span);
        Assert.DoesNotContain("earlier line", error.Message, StringComparison.Ordinal);
        Assert.Contains("scalar operand", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public async Task ConsecutiveLineFinalStars_ChainAsMultiplicationDetached_AndAreSeparateRowsAttached()
    {
        // `A *` newline `B *` newline `C*`: the two detached stars multiply; the spread `C*` is the
        // misplaced right operand — reported once, at `C*`.
        var error = Assert.Single(SourceProvenance.ExpectFrontEndError("A = 1, 2\nB = 3, 4\nC = 5, 6\nA *\nB *\nC*, 0"));
        Assert.Equal(DiagnosticCode.MisplacedSpread, error.Code);
        Assert.Equal(new SourceSpan(6, 1, 6, 3), error.Span);
        Assert.Contains("is separated from its left operand", error.Message, StringComparison.Ordinal);

        // Attached, every line is a completed spread row of its own.
        const string attached = "A = 1, 2\nB = 3, 4\nC = 5, 6\nA*\nB*\nC*";
        Assert.Equal("spread(A) | spread(B) | spread(C)", Rows(ParseWithoutAnyDiagnostic(attached).Root));
        Assert.Equal("S[1, 2, 3, 4, 5, 6]", await ValueOnEveryRoute(attached));
    }

    // Explicitly close only the intended misplaced spread, preserving all
    // preceding line-final multiplication and original diagnostic spans.
    private static string CloseLastSpread(string source)
        => source.Insert(source.LastIndexOf('*') + 1, ", 0");
}
