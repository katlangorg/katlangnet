using KatLang.Optimizations.Sequences;
using System.Numerics;

namespace KatLang.Tests;

/// <summary>
/// Regression coverage for the iterative, output-bounded diagnostic
/// expression-name renderer (<see cref="ExprNameRenderer"/>). The golden cases pin
/// byte-identical rendering for ordinary-depth names in every mode (the renderer
/// replaced per-mode RECURSIVE helpers, so these are the compatibility contract);
/// the deep cases pin stack safety, deterministic elision, and the output bound for
/// the shapes the evaluator's structural gates deliberately accept at any depth.
/// </summary>
public class ExprNameRendererTests
{
    private static string Open(Expr e) => ExprNameRenderer.Render(e, ExprNameMode.Open);
    private static string Diag(Expr e) => ExprNameRenderer.Render(e, ExprNameMode.DiagnosticName);

    private static Expr JoinChain(int joins)
    {
        Expr chain = new Expr.SequenceConstruct(new Expr.Num(1), new Expr.Num(2));
        for (var i = 0; i < joins; i++)
            chain = new Expr.SequenceConstruct(chain, new Expr.Num(3));
        return chain;
    }

    private static Expr SpreadChain(int spreads)
    {
        Expr chain = new Expr.Num(7);
        for (var i = 0; i < spreads; i++)
            chain = new Expr.SequenceSpread(chain);
        return chain;
    }

    // ── Golden byte-identity for ordinary-depth names ───────────────────────────

    [Fact]
    public void Golden_LeavesAndSimpleComposites_RenderExactly()
    {
        Assert.Equal("x", Open(new Expr.Resolve("x")));
        Assert.Equal("p", Open(new Expr.Param("p")));
        Assert.Equal("1.5", Open(new Expr.Num(1.5m)));
        Assert.Equal("-2", Open(new Expr.Num(-2m)));
        Assert.Equal("'s'", Open(new Expr.StringLiteral("s")));
        Assert.Equal("{...}", Open(new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [], []))));
        Assert.Equal("(1, x)", Open(new Expr.Capture(OutputBundle.From([new Expr.Num(1m), new Expr.Resolve("x")]))));
        Assert.Equal("()", Open(new Expr.Capture(OutputBundle.Empty)));
        Assert.Equal("()", Open(new Expr.EmptySequence(0)));
        Assert.Equal("((()))", Open(new Expr.EmptySequence(2)));
        Assert.Equal("(nativeCall)", Open(new Expr.NativeCall("sin", ["x"])));
    }

    [Fact]
    public void Golden_OperatorAndPostfixForms_RenderExactly()
    {
        var a = new Expr.Resolve("a");
        var b = new Expr.Resolve("b");

        // Unary operand wrapping: leaves and tighter-binding postfix forms stay bare.
        Assert.Equal("-a", Open(new Expr.Unary(UnaryOp.Minus, a)));
        Assert.Equal("not a", Open(new Expr.Unary(UnaryOp.Not, a)));
        Assert.Equal("-a.f", Open(new Expr.Unary(UnaryOp.Minus, new Expr.DotCall(a, "f", null))));
        Assert.Equal(
            "-((a + b))",
            Open(new Expr.Unary(UnaryOp.Minus, new Expr.Binary(BinaryOp.Add, a, b))));
        Assert.Equal("-(-a)", Open(new Expr.Unary(UnaryOp.Minus, new Expr.Unary(UnaryOp.Minus, a))));

        // Binary open names self-parenthesize.
        Assert.Equal("(a + b)", Open(new Expr.Binary(BinaryOp.Add, a, b)));
        Assert.Equal("(a div b)", Open(new Expr.Binary(BinaryOp.IDiv, a, b)));

        // Indexing renders postfix `target:selector` with rebinding-aware wrapping.
        Assert.Equal("a:0", Open(new Expr.Index(a, new Expr.Num(0))));
        Assert.Equal("(-a):(-1)", Open(new Expr.Index(
            new Expr.Unary(UnaryOp.Minus, a), new Expr.Num(-1m))));
        Assert.Equal("a:0:1", Open(new Expr.Index(
            new Expr.Index(a, new Expr.Num(0)), new Expr.Num(1))));
        Assert.Equal("a:(b:0)", Open(new Expr.Index(a, new Expr.Index(b, new Expr.Num(0)))));
        Assert.Equal("a:(b*)", Open(new Expr.Index(a, new Expr.SequenceSpread(b))));

        // Calls and dot-calls.
        var emptyArgs = OutputBundle.Empty;
        Assert.Equal("f(...)", Open(new Expr.Call(new Expr.Resolve("f"), emptyArgs)));
        Assert.Equal("a.f", Open(new Expr.DotCall(a, "f", null)));
        Assert.Equal("a.f(...)", Open(new Expr.DotCall(a, "f", emptyArgs)));

        // Grace prefix/postfix.
        Assert.Equal("~a", Open(new Expr.Grace(a, -1)));
        Assert.Equal("a~", Open(new Expr.Grace(a, 1)));

        // Spread: unary operands re-parenthesize, everything else stays bare.
        Assert.Equal("a*", Open(new Expr.SequenceSpread(a)));
        Assert.Equal("(-a)*", Open(new Expr.SequenceSpread(new Expr.Unary(UnaryOp.Minus, a))));

        // Lists and internal joins.
        Assert.Equal("[a, b]", Open(new Expr.ListLiteral([a, b])));
        Assert.Equal("[]", Open(new Expr.ListLiteral([])));
        Assert.Equal("(1, 2)", Open(new Expr.SequenceConstruct(new Expr.Num(1), new Expr.Num(2))));
    }

    [Fact]
    public void Golden_NotOperandParenthesization_RendersExactly()
    {
        var a = new Expr.Resolve("a");
        var b = new Expr.Resolve("b");
        var notA = new Expr.Unary(UnaryOp.Not, a);
        var notB = new Expr.Unary(UnaryOp.Not, b);

        // `not` binds below the comparisons and above the logical operators
        // (comparisons > not > and > xor > or), so a `not` operand keeps parentheses
        // under every tighter operator, on either side, and renders bare under
        // `and`/`xor`/`or` — otherwise `not a == b` would read back as `not (a == b)`.
        Assert.Equal("((not a) == b)", Open(EvaluatorTestSupport.Compare(ComparisonOp.Eq, notA, b)));
        Assert.Equal("(a == (not b))", Open(EvaluatorTestSupport.Compare(ComparisonOp.Eq, a, notB)));
        Assert.Equal("((not a) > b)", Open(EvaluatorTestSupport.Compare(ComparisonOp.Gt, notA, b)));
        Assert.Equal("((not a) + b)", Open(new Expr.Binary(BinaryOp.Add, notA, b)));
        Assert.Equal("(a * (not b))", Open(new Expr.Binary(BinaryOp.Mul, a, notB)));
        Assert.Equal("(a ^ (not b))", Open(new Expr.Binary(BinaryOp.Pow, a, notB)));
        Assert.Equal("(not a and b)", Open(new Expr.Binary(BinaryOp.And, notA, b)));
        Assert.Equal("(a or not b)", Open(new Expr.Binary(BinaryOp.Or, a, notB)));
        Assert.Equal("(not a xor b)", Open(new Expr.Binary(BinaryOp.Xor, notA, b)));

        // DiagnosticName mode renders the chain bare with the same operand wrapping.
        Assert.Equal("(not a) == b", Diag(EvaluatorTestSupport.Compare(ComparisonOp.Eq, notA, b)));
        Assert.Equal("a == (not b)", Diag(EvaluatorTestSupport.Compare(ComparisonOp.Eq, a, notB)));
        Assert.Equal("not a and b", Diag(new Expr.Binary(BinaryOp.And, notA, b)));
        Assert.Equal("(not a) == b", ExprNameRenderer.RenderComparisonLinkDiagnosticName(ComparisonOp.Eq, notA, b));

        // Negating a comparison keeps the established unary-operand wrapping, which
        // reads back as the same tree under this precedence; a `not` under unary
        // minus keeps its parentheses, because bare `-not a` is not an operand at all.
        Assert.Equal("not ((a > b))", Open(new Expr.Unary(UnaryOp.Not, EvaluatorTestSupport.Compare(ComparisonOp.Gt, a, b))));
        Assert.Equal("-(not a)", Open(new Expr.Unary(UnaryOp.Minus, notA)));
        Assert.Equal("not (not a)", Open(new Expr.Unary(UnaryOp.Not, notA)));
    }

    [Fact]
    public void Golden_PowerBaseParenthesization_RendersExactly()
    {
        var a = new Expr.Resolve("a");
        var b = new Expr.Resolve("b");

        // `^` binds tighter than prefix unary on the LEFT, so a unary base —
        // and a literal that renders with a leading minus — must keep its
        // parentheses: bare `-a ^ b` reads back as `-(a ^ b)`.
        Assert.Equal("((-a) ^ b)", Open(new Expr.Binary(BinaryOp.Pow, new Expr.Unary(UnaryOp.Minus, a), b)));
        Assert.Equal("((not a) ^ b)", Open(new Expr.Binary(BinaryOp.Pow, new Expr.Unary(UnaryOp.Not, a), b)));
        Assert.Equal("((-2) ^ b)", Open(new Expr.Binary(BinaryOp.Pow, new Expr.Num(-2m), b)));

        // The exponent side is the unary level, so a unary or negative-literal
        // exponent stays bare — `a ^ -b` reads back with the same AST.
        Assert.Equal("(a ^ -b)", Open(new Expr.Binary(BinaryOp.Pow, a, new Expr.Unary(UnaryOp.Minus, b))));
        Assert.Equal("(a ^ -2)", Open(new Expr.Binary(BinaryOp.Pow, a, new Expr.Num(-2m))));

        // Non-negative literal and self-delimiting bases render as before.
        Assert.Equal("(2 ^ b)", Open(new Expr.Binary(BinaryOp.Pow, new Expr.Num(2m), b)));
        Assert.Equal(
            "((a + b) ^ b)",
            Open(new Expr.Binary(BinaryOp.Pow, new Expr.Binary(BinaryOp.Add, a, b), b)));

        // Negating a whole power keeps the established unary-operand wrapping.
        Assert.Equal(
            "-((a ^ b))",
            Open(new Expr.Unary(UnaryOp.Minus, new Expr.Binary(BinaryOp.Pow, a, b))));

        // DiagnosticName mode renders the chain bare but still wraps a
        // rebinding power base, keeping capture bundles in their
        // sequence-value spelling.
        Assert.Equal(
            "(-a) ^ b",
            ExprNameRenderer.RenderBinaryDiagnosticName(BinaryOp.Pow, new Expr.Unary(UnaryOp.Minus, a), b));
        Assert.Equal(
            "(-2) ^ b",
            ExprNameRenderer.RenderBinaryDiagnosticName(BinaryOp.Pow, new Expr.Num(-2m), b));
        Assert.Equal(
            "a ^ -b",
            ExprNameRenderer.RenderBinaryDiagnosticName(BinaryOp.Pow, a, new Expr.Unary(UnaryOp.Minus, b)));
        Assert.Equal(
            "2 ^ 3 ^ 2",
            Diag(new Expr.Binary(
                BinaryOp.Pow,
                new Expr.Num(2),
                new Expr.Binary(BinaryOp.Pow, new Expr.Num(3), new Expr.Num(2)))));
        Assert.Equal(
            "(1, 2) ^ b",
            Diag(new Expr.Binary(BinaryOp.Pow, new Expr.Capture([new Expr.Num(1), new Expr.Num(2)]), b)));
    }

    [Fact]
    public void Golden_PowerBaseParenthesization_CoversDecimal128SpecialValues()
    {
        var a = new Expr.Resolve("a");
        var b = new Expr.Resolve("b");

        // Host-built numeric literals can carry values that source literals
        // cannot spell. Parenthesization follows the rendered sign: negative
        // zero and negative infinity need a protected power base, while
        // positive infinity and NaN render without a leading minus.
        Assert.Equal(
            "((-0) ^ b)",
            Open(new Expr.Binary(BinaryOp.Pow, new Expr.Num(Decimal128.NegativeZero), b)));
        Assert.Equal(
            "((-Infinity) ^ b)",
            Open(new Expr.Binary(BinaryOp.Pow, new Expr.Num(Decimal128.NegativeInfinity), b)));
        Assert.Equal(
            "(Infinity ^ b)",
            Open(new Expr.Binary(BinaryOp.Pow, new Expr.Num(Decimal128.PositiveInfinity), b)));
        Assert.Equal(
            "(NaN ^ b)",
            Open(new Expr.Binary(BinaryOp.Pow, new Expr.Num(Decimal128.NaN), b)));

        Assert.Equal(
            "(-0) ^ b",
            ExprNameRenderer.RenderBinaryDiagnosticName(
                BinaryOp.Pow, new Expr.Num(Decimal128.NegativeZero), b));
        Assert.Equal(
            "(-Infinity) ^ b",
            ExprNameRenderer.RenderBinaryDiagnosticName(
                BinaryOp.Pow, new Expr.Num(Decimal128.NegativeInfinity), b));
        Assert.Equal(
            "Infinity ^ b",
            ExprNameRenderer.RenderBinaryDiagnosticName(
                BinaryOp.Pow, new Expr.Num(Decimal128.PositiveInfinity), b));
        Assert.Equal(
            "NaN ^ b",
            ExprNameRenderer.RenderBinaryDiagnosticName(
                BinaryOp.Pow, new Expr.Num(Decimal128.NaN), b));

        // The exponent remains the unary-accepting side, so signed host
        // literals stay bare there just like the ordinary `a ^ -2` case.
        Assert.Equal(
            "(a ^ -0)",
            Open(new Expr.Binary(BinaryOp.Pow, a, new Expr.Num(Decimal128.NegativeZero))));
        Assert.Equal(
            "(a ^ -Infinity)",
            Open(new Expr.Binary(BinaryOp.Pow, a, new Expr.Num(Decimal128.NegativeInfinity))));

        // Index-selector mode uses the same rendered-sign predicate: signed
        // values need parentheses because a selector is primary syntax, but
        // NaN's diagnostic spelling is unsigned even when its IEEE sign bit
        // is set.
        Assert.Equal(
            "a:(-Infinity)",
            Open(new Expr.Index(a, new Expr.Num(Decimal128.NegativeInfinity))));
        Assert.Equal(
            "a:NaN",
            Open(new Expr.Index(a, new Expr.Num(Decimal128.NaN))));
    }

    [Fact]
    public void Golden_DiagnosticNameMode_RendersExactly()
    {
        var one = new Expr.Num(1);
        var two = new Expr.Num(2);

        // Top-level binary chains render bare, nested ones stay bare through the
        // chain (matching the former recursive ExprDiagnosticName).
        Assert.Equal("1 + 2", ExprNameRenderer.RenderBinaryDiagnosticName(BinaryOp.Add, one, two));
        Assert.Equal(
            "1 + 2 + 3",
            Diag(new Expr.Binary(BinaryOp.Add, new Expr.Binary(BinaryOp.Add, one, two), new Expr.Num(3))));

        // Zero-shape blocks render as one written sequence value over their outputs.
        Assert.Equal(
            "(1, 2)",
            Diag(new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [], [one, two]))));
        Assert.Equal("()", Diag(new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [], []))));

        // Internal joins render as one sequence value.
        Assert.Equal(
            "((1, 2), 3)",
            Diag(new Expr.SequenceConstruct(new Expr.SequenceConstruct(one, two), new Expr.Num(3))));

        // Everything else falls back to the Open spelling.
        Assert.Equal("a.f", Diag(new Expr.DotCall(new Expr.Resolve("a"), "f", null)));
    }

    [Fact]
    public void Golden_ComparisonChains_RenderExactly()
    {
        var a = new Expr.Resolve("a");
        var b = new Expr.Resolve("b");
        var c = new Expr.Resolve("c");
        var d = new Expr.Resolve("d");
        var chain = EvaluatorTestSupport.Chain(a, ComparisonOp.Lt, b, ComparisonOp.Le, c, ComparisonOp.Eq, d);

        // A chain renders as the flat chain it is — never nested comparisons — in both
        // modes; the Open spelling self-parenthesizes like a binary name.
        Assert.Equal("a < b <= c == d", Diag(chain));
        Assert.Equal("(a < b <= c == d)", Open(chain));

        // Parentheses that change chain boundaries are preserved: a nested chain is a
        // parenthesized operand, so the three groupings render distinctly.
        Assert.Equal("a < b == true", Diag(EvaluatorTestSupport.Chain(a, ComparisonOp.Lt, b, ComparisonOp.Eq, new Expr.BoolLiteral(true))));
        Assert.Equal("(a < b) == true", Diag(EvaluatorTestSupport.Compare(ComparisonOp.Eq, EvaluatorTestSupport.Compare(ComparisonOp.Lt, a, b), new Expr.BoolLiteral(true))));
        Assert.Equal("a < (b == true)", Diag(EvaluatorTestSupport.Compare(ComparisonOp.Lt, a, EvaluatorTestSupport.Compare(ComparisonOp.Eq, b, new Expr.BoolLiteral(true)))));
        Assert.Equal("(a < b) == (c < d)", Diag(EvaluatorTestSupport.Compare(ComparisonOp.Eq, EvaluatorTestSupport.Compare(ComparisonOp.Lt, a, b), EvaluatorTestSupport.Compare(ComparisonOp.Lt, c, d))));
        Assert.Equal("((a < b) == true)", Open(EvaluatorTestSupport.Compare(ComparisonOp.Eq, EvaluatorTestSupport.Compare(ComparisonOp.Lt, a, b), new Expr.BoolLiteral(true))));

        // Chain operands: `not` and the logical operators keep their parentheses;
        // arithmetic, powers, prefix minus, and postfix forms read back bare.
        Assert.Equal("a == (b and c)", Diag(EvaluatorTestSupport.Compare(ComparisonOp.Eq, a, new Expr.Binary(BinaryOp.And, b, c))));
        Assert.Equal("a + b < c * d", Diag(EvaluatorTestSupport.Compare(ComparisonOp.Lt, new Expr.Binary(BinaryOp.Add, a, b), new Expr.Binary(BinaryOp.Mul, c, d))));
        Assert.Equal("-a ^ b < c", Diag(EvaluatorTestSupport.Compare(ComparisonOp.Lt, new Expr.Unary(UnaryOp.Minus, new Expr.Binary(BinaryOp.Pow, a, b)), c)));
        Assert.Equal("a:0 < b.c", Diag(EvaluatorTestSupport.Compare(ComparisonOp.Lt, new Expr.Index(a, new Expr.Num(0)), new Expr.DotCall(b, "c", null))));

        // A chain under a tighter operator, under prefix minus, and under `not`.
        Assert.Equal("(a < b) + c", Diag(new Expr.Binary(BinaryOp.Add, EvaluatorTestSupport.Compare(ComparisonOp.Lt, a, b), c)));
        Assert.Equal("(a < b) ^ c", Diag(new Expr.Binary(BinaryOp.Pow, EvaluatorTestSupport.Compare(ComparisonOp.Lt, a, b), c)));
        Assert.Equal("-(a < b)", Diag(new Expr.Unary(UnaryOp.Minus, EvaluatorTestSupport.Compare(ComparisonOp.Lt, a, b))));
        Assert.Equal("not a < b < c", Diag(new Expr.Unary(UnaryOp.Not, EvaluatorTestSupport.Chain(a, ComparisonOp.Lt, b, ComparisonOp.Lt, c))));
        Assert.Equal("a < b and c < d", Diag(new Expr.Binary(BinaryOp.And, EvaluatorTestSupport.Compare(ComparisonOp.Lt, a, b), EvaluatorTestSupport.Compare(ComparisonOp.Lt, c, d))));

        // Postfix positions parenthesize a chain like a binary (Lean twin: the
        // `postfixTargetName` goldens in CoreTests comparisonChainDiagnosticNames).
        Assert.Equal("(a < b):0", Open(new Expr.Index(EvaluatorTestSupport.Compare(ComparisonOp.Lt, a, b), new Expr.Num(0))));
        Assert.Equal("(a < b).count", Diag(new Expr.DotCall(EvaluatorTestSupport.Compare(ComparisonOp.Lt, a, b), "count", null)));
        Assert.Equal("(a + b)(...)", Diag(new Expr.Call(new Expr.Binary(BinaryOp.Add, a, b), OutputBundle.Empty)));
        Assert.Equal("a:(b < c)", Open(new Expr.Index(a, EvaluatorTestSupport.Compare(ComparisonOp.Lt, b, c))));
        Assert.Equal("(a < b)*", Open(new Expr.SequenceSpread(EvaluatorTestSupport.Compare(ComparisonOp.Lt, a, b))));

        // One link's name is exactly its two adjacent operands.
        Assert.Equal("2 < true", ExprNameRenderer.RenderComparisonLinkDiagnosticName(ComparisonOp.Lt, new Expr.Num(2), new Expr.BoolLiteral(true)));
        Assert.Equal("(1, 2) < (1, 2)", ExprNameRenderer.RenderComparisonLinkDiagnosticName(
            ComparisonOp.Lt, new Expr.Capture([new Expr.Num(1), new Expr.Num(2)]), new Expr.Capture([new Expr.Num(1), new Expr.Num(2)])));
        Assert.Equal("(a < b) == c", ExprNameRenderer.RenderComparisonLinkDiagnosticName(ComparisonOp.Eq, EvaluatorTestSupport.Compare(ComparisonOp.Lt, a, b), c));
    }

    [Fact]
    public void Golden_DiagnosticNameMode_IsPrecedenceFaithful()
    {
        var a = new Expr.Resolve("a");
        var b = new Expr.Resolve("b");
        var c = new Expr.Resolve("c");

        // Operand-shape names keep exactly the parentheses the ladder needs, so the
        // text reads back as the rendered AST (Lean twin: CoreTests
        // binaryDiagnosticNamesReadBackFaithfully).
        Assert.Equal("a + b + c", Diag(new Expr.Binary(BinaryOp.Add, new Expr.Binary(BinaryOp.Add, a, b), c)));
        Assert.Equal("a - (b - c)", Diag(new Expr.Binary(BinaryOp.Sub, a, new Expr.Binary(BinaryOp.Sub, b, c))));
        Assert.Equal("(a + b) * c", Diag(new Expr.Binary(BinaryOp.Mul, new Expr.Binary(BinaryOp.Add, a, b), c)));
        Assert.Equal("a + b * c", Diag(new Expr.Binary(BinaryOp.Add, a, new Expr.Binary(BinaryOp.Mul, b, c))));
        Assert.Equal("(a ^ b) ^ c", Diag(new Expr.Binary(BinaryOp.Pow, new Expr.Binary(BinaryOp.Pow, a, b), c)));
        Assert.Equal("a ^ b ^ c", Diag(new Expr.Binary(BinaryOp.Pow, a, new Expr.Binary(BinaryOp.Pow, b, c))));
        Assert.Equal("(a + b) ^ c", Diag(new Expr.Binary(BinaryOp.Pow, new Expr.Binary(BinaryOp.Add, a, b), c)));
        Assert.Equal("(a or b) and c", Diag(new Expr.Binary(BinaryOp.And, new Expr.Binary(BinaryOp.Or, a, b), c)));
        Assert.Equal("a or b and c", Diag(new Expr.Binary(BinaryOp.Or, a, new Expr.Binary(BinaryOp.And, b, c))));
        Assert.Equal("-(a + b)", Diag(new Expr.Unary(UnaryOp.Minus, new Expr.Binary(BinaryOp.Add, a, b))));
        Assert.Equal("-a ^ b", Diag(new Expr.Unary(UnaryOp.Minus, new Expr.Binary(BinaryOp.Pow, a, b))));
        Assert.Equal("-(-a)", Diag(new Expr.Unary(UnaryOp.Minus, new Expr.Unary(UnaryOp.Minus, a))));
        Assert.Equal("-(not a)", Diag(new Expr.Unary(UnaryOp.Minus, new Expr.Unary(UnaryOp.Not, a))));
        Assert.Equal("not not a", Diag(new Expr.Unary(UnaryOp.Not, new Expr.Unary(UnaryOp.Not, a))));
        Assert.Equal("not (a and b)", Diag(new Expr.Unary(UnaryOp.Not, new Expr.Binary(BinaryOp.And, a, b))));
        Assert.Equal("not a < b", Diag(new Expr.Unary(UnaryOp.Not, EvaluatorTestSupport.Compare(ComparisonOp.Lt, a, b))));
        Assert.Equal("-a + b", Diag(new Expr.Binary(BinaryOp.Add, new Expr.Unary(UnaryOp.Minus, a), b)));
        Assert.Equal("-a.f", Diag(new Expr.Unary(UnaryOp.Minus, new Expr.DotCall(a, "f", null))));
        Assert.Equal("-(1, 2)", Diag(new Expr.Unary(UnaryOp.Minus, new Expr.Capture([new Expr.Num(1), new Expr.Num(2)]))));

        // The Open spelling is untouched: composites self-parenthesize there.
        Assert.Equal("((a + b) * c)", Open(new Expr.Binary(BinaryOp.Mul, new Expr.Binary(BinaryOp.Add, a, b), c)));
        Assert.Equal("-((a + b))", Open(new Expr.Unary(UnaryOp.Minus, new Expr.Binary(BinaryOp.Add, a, b))));
    }

    [Fact]
    public void Golden_EvaluatorErrorMessages_AreUnchangedAtOrdinaryDepth()
    {
        // End-to-end pin through public evaluation: the binary operand-shape context
        // renders exactly as before the iterative renderer.
        var join = new Expr.SequenceConstruct(
            new Expr.SequenceConstruct(new Expr.Num(1), new Expr.Num(2)), new Expr.Num(3));
        var result = Evaluator.Run(new Expr.Binary(BinaryOp.Add, join, new Expr.Num(1)));
        Assert.True(result.IsError);
        var withContext = Assert.IsType<EvalError.WithContext>(result.Error);
        Assert.Equal("while evaluating `((1, 2), 3) + 1`", withContext.ErrorContext.ToString());
    }

    // ── Bounded, deterministic deep rendering ───────────────────────────────────

    public static TheoryData<string> DeepShapes => new(
        "join", "spread", "binaryLeft", "binaryRight", "unary", "index",
        "dotcall", "call", "gracePost", "list", "blockOutput");

    private static Expr BuildDeepShape(string shape, int levels)
    {
        Expr expr = new Expr.Num(1);
        for (var i = 0; i < levels; i++)
        {
            expr = shape switch
            {
                "join" => new Expr.SequenceConstruct(expr, new Expr.Num(1)),
                "spread" => new Expr.SequenceSpread(expr),
                "binaryLeft" => new Expr.Binary(BinaryOp.Add, expr, new Expr.Num(1)),
                "binaryRight" => new Expr.Binary(BinaryOp.Add, new Expr.Num(1), expr),
                "unary" => new Expr.Unary(UnaryOp.Minus, expr),
                "index" => new Expr.Index(expr, new Expr.Num(0)),
                "dotcall" => new Expr.DotCall(expr, "f", null),
                "call" => new Expr.Call(expr, OutputBundle.Empty),
                "gracePost" => new Expr.Grace(expr, 1),
                "list" => new Expr.ListLiteral([expr]),
                "blockOutput" => new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [], [expr])),
                _ => throw new InvalidOperationException(shape),
            };
        }

        return expr;
    }

    [Theory]
    [MemberData(nameof(DeepShapes))]
    public void DeepChains_RenderBoundedAndDeterministic_InEveryMode(string shape)
    {
        // 200,000 levels of every recursively renderable shape: the former recursive
        // renderers overflowed the process here; the engine must return a bounded,
        // reproducible name without depth-proportional stack.
        var deep = BuildDeepShape(shape, 200_000);
        foreach (var mode in new[]
        {
            ExprNameMode.Open, ExprNameMode.DiagnosticName, ExprNameMode.UnaryOperand,
            ExprNameMode.SpreadOperand, ExprNameMode.IndexTarget, ExprNameMode.IndexSelector,
        })
        {
            var first = ExprNameRenderer.Render(deep, mode);
            var second = ExprNameRenderer.Render(deep, mode);
            Assert.Equal(first, second);
            Assert.True(
                first.Length <= ExprNameRenderer.MaxRenderedNameLength + ExprNameRenderer.TruncationMarker.Length,
                $"{shape}/{mode} rendered {first.Length} units");

            // Every deep shape elides — except a block outside DiagnosticName mode,
            // which is an opaque "{...}" leaf by the established rules.
            if (shape != "blockOutput" || mode == ExprNameMode.DiagnosticName)
                Assert.EndsWith(ExprNameRenderer.TruncationMarker, first);
        }
    }

    [Fact]
    public void DeepChains_ThroughEvaluatorNameHelpers_AreBounded()
    {
        // The shared internal helpers used by the evaluator AND the optimizer reason
        // strings (LoopExprPlan, SequencePipelineOptimizer summaries) all route
        // through the same engine.
        var joined = Evaluator.OpenExprName(JoinChain(200_000));
        Assert.True(joined.Length <= ExprNameRenderer.MaxRenderedNameLength + 1);

        var spread = Evaluator.OpenExprName(SpreadChain(200_000));
        Assert.True(spread.Length <= ExprNameRenderer.MaxRenderedNameLength + 1);
    }

    [Fact]
    public void HostileLeafPayloads_AreCappedWithoutMaterializing()
    {
        // A giant identifier or literal is truncated at the bound.
        var bigName = new string('n', 100_000);
        var rendered = Open(new Expr.Resolve(bigName));
        Assert.Equal(
            bigName[..ExprNameRenderer.MaxRenderedNameLength] + ExprNameRenderer.TruncationMarker,
            rendered);

        var bigLiteral = Open(new Expr.StringLiteral(new string('s', 100_000)));
        Assert.True(bigLiteral.Length <= ExprNameRenderer.MaxRenderedNameLength + 1);
        Assert.StartsWith("'sss", bigLiteral);

        // EmptySequence depth is host-controlled: the former renderer materialized
        // 2*(depth+1) characters (or threw on negatives); the engine caps the run
        // and never allocates proportional storage.
        var hugeEmpty = Open(new Expr.EmptySequence(int.MaxValue));
        Assert.True(hugeEmpty.Length <= ExprNameRenderer.MaxRenderedNameLength + 1);
        var negativeEmpty = Open(new Expr.EmptySequence(-5));
        Assert.Equal(string.Empty, negativeEmpty);
    }

    [Fact]
    public void Truncation_DoesNotSplitValidUtf16SurrogatePairs()
    {
        // Put an astral scalar exactly across the 512-unit boundary. The old
        // substring-at-room implementation retained only its high surrogate and
        // therefore manufactured ill-formed UTF-16 in the diagnostic.
        var boundaryName = new string('n', ExprNameRenderer.MaxRenderedNameLength - 1)
            + "😀tail";
        var renderedName = Open(new Expr.Resolve(boundaryName));
        Assert.Equal(
            new string('n', ExprNameRenderer.MaxRenderedNameLength - 1)
                + ExprNameRenderer.TruncationMarker,
            renderedName);
        Assert.False(HasUnpairedSurrogate(renderedName));

        // The same boundary through the general text append path (the opening quote
        // has already consumed one unit before the string payload is appended).
        var boundaryLiteral = new string('s', ExprNameRenderer.MaxRenderedNameLength - 2)
            + "😀tail";
        var renderedLiteral = Open(new Expr.StringLiteral(boundaryLiteral));
        Assert.EndsWith(ExprNameRenderer.TruncationMarker, renderedLiteral);
        Assert.False(HasUnpairedSurrogate(renderedLiteral));

        static bool HasUnpairedSurrogate(string text)
        {
            for (var i = 0; i < text.Length; i++)
            {
                if (char.IsHighSurrogate(text[i]))
                {
                    if (i + 1 >= text.Length || !char.IsLowSurrogate(text[++i]))
                        return true;
                }
                else if (char.IsLowSurrogate(text[i]))
                {
                    return true;
                }
            }

            return false;
        }
    }

    [Fact]
    public void WideCollections_RenderWithinTheOutputBound()
    {
        // The list/output collections the renderer walks are OutputBundles,
        // whose membership is snapshotted eagerly at construction — a lying or
        // lazily-throwing IReadOnlyList can no longer reach the renderer
        // through these surfaces at all (it fails at bundle construction, see
        // OutputBundleOwnershipTests). What remains to pin here is the output
        // bound itself: a genuinely wide collection renders no more than the
        // 512-unit cap plus the truncation marker, in both renderer modes.
        var wideItems = OutputBundle.TakeOwnership(
            [.. Enumerable.Repeat<Expr>(new Expr.Num(1), 50_000)]);
        var list = Open(new Expr.ListLiteral(wideItems));
        Assert.EndsWith(ExprNameRenderer.TruncationMarker, list);
        Assert.True(list.Length <= ExprNameRenderer.MaxRenderedNameLength + 1);

        var block = Diag(new Expr.AlgorithmExpr(new Algorithm.User(
            null, [], [], [], wideItems)));
        Assert.EndsWith(ExprNameRenderer.TruncationMarker, block);
        Assert.True(block.Length <= ExprNameRenderer.MaxRenderedNameLength + 1);
    }

    [Fact]
    public void InBoundNames_NeverCarryTheTruncationMarker()
    {
        // A name that fits the bound renders fully — elision is deterministic and
        // only ever appears past the bound.
        var chain = JoinChain(20);
        var rendered = Open(chain);
        Assert.DoesNotContain(ExprNameRenderer.TruncationMarker, rendered);
        Assert.StartsWith("(((", rendered);
        Assert.EndsWith(", 3)", rendered);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SuccessfulResolvedCalls_DoNotRenderDiagnosticNames_InEitherEvaluationMode(
        bool enableOptimizations)
    {
        var ordinary = new Expr.Call(
            new Expr.Resolve("count"),
            Arguments(new Expr.ListLiteral([new Expr.Num(1), new Expr.Num(2)])));
        var dotted = new Expr.DotCall(
            new Expr.ListLiteral([new Expr.Num(1), new Expr.Num(2)]),
            "count",
            null);

        foreach (var (expression, expected) in new (Expr Expression, decimal Expected)[]
        {
            (ordinary, 2m),
            (dotted, 2m),
        })
        {
            var flatObservations = new EvaluationObservations();
            var flat = Evaluator.RunObserved(expression, flatObservations, enableOptimizations);
            Assert.False(flat.IsError);
            Assert.Equal([expected], flat.Value.ToAtoms());
            Assert.Equal(0, flatObservations.CallDiagnosticNameRenderCount);

            var countedObservations = new EvaluationObservations();
            var (counted, _) = Evaluator.RunCountedObserved(
                expression,
                enableOptimizations: enableOptimizations,
                observations: countedObservations);
            Assert.False(counted.IsError);
            Assert.Equal([expected], counted.Value.Value.ToAtoms());
            Assert.Equal(1, counted.Value.EmittedCount);
            Assert.Equal(0, countedObservations.CallDiagnosticNameRenderCount);
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SuccessfulDeepCompoundCallee_DoesNotRenderDiagnosticName(
        bool enableOptimizations)
    {
        const int joins = 50_000;
        var call = SuccessfulComplexCalleeCall(joins);

        var flatObservations = new EvaluationObservations();
        var flat = Evaluator.RunObserved(call, flatObservations, enableOptimizations);
        Assert.False(flat.IsError);
        Assert.Equal([joins + 2m], flat.Value.ToAtoms());
        Assert.Equal(0, flatObservations.CallDiagnosticNameRenderCount);

        var countedObservations = new EvaluationObservations();
        var (counted, _) = Evaluator.RunCountedObserved(
            call,
            enableOptimizations: enableOptimizations,
            observations: countedObservations);
        Assert.False(counted.IsError);
        Assert.Equal([joins + 2m], counted.Value.Value.ToAtoms());
        Assert.Equal(1, counted.Value.EmittedCount);
        Assert.Equal(0, countedObservations.CallDiagnosticNameRenderCount);
    }

    [Fact]
    public void SuccessfulFusedPipeline_DoesNotRenderDiagnosticContext()
    {
        var parse = Parser.Parse("B(x) = x > 5\nrange(1, 10).filter(B).count");
        Assert.False(parse.HasErrors);
        var diagnostics = new SequencePipelineDiagnostics();
        var observations = new EvaluationObservations();

        var (result, _) = Evaluator.RunCountedObserved(
            new Expr.AlgorithmExpr(parse.Root),
            enableOptimizations: true,
            sequenceDiagnostics: diagnostics,
            observations: observations);

        Assert.False(result.IsError);
        Assert.Equal([5m], result.Value.Value.ToAtoms());
        Assert.Equal(1, diagnostics.GetSnapshot().FilterCountFusionHits);
        Assert.Equal(0, observations.CallDiagnosticNameRenderCount);
    }

    [Fact]
    public void OrdinaryAndDottedFailures_RetainExactDiagnosticNamesAndText()
    {
        var receiver = JoinChain(2);
        var compoundFunction = new Expr.DotCall(receiver, "count", null);
        var ordinaryFailure = new Expr.Call(compoundFunction, Arguments(new Expr.Num(9)));
        var ordinaryName = Open(compoundFunction);
        var ordinaryObservations = new EvaluationObservations();

        var ordinary = Evaluator.RunObserved(ordinaryFailure, ordinaryObservations);
        Assert.True(ordinary.IsError);
        var ordinaryContext = Assert.IsType<EvalError.WithContext>(ordinary.Error);
        Assert.Equal(
            $"while evaluating call to {ordinaryName}",
            ordinaryContext.ErrorContext.ToString());
        var ordinaryArity = Assert.IsType<EvalError.ArityMismatch>(ordinaryContext.Inner);
        Assert.Equal(ordinaryName, ordinaryArity.Signature?.DisplayText);
        Assert.Equal(
            $"Callable `{ordinaryName}` expects 0 arguments, but was called with 1 argument.",
            KatLangError.FromEvalError(ordinary.Error).Message);
        Assert.Equal(2, ordinaryObservations.CallDiagnosticNameRenderCount);

        var dottedFailure = new Expr.DotCall(receiver, "take", Arguments());
        var receiverName = Open(receiver);
        var dottedObservations = new EvaluationObservations();
        var dotted = Evaluator.RunObserved(dottedFailure, dottedObservations);
        Assert.True(dotted.IsError);
        var dottedContext = Assert.IsType<EvalError.WithContext>(dotted.Error);
        Assert.Equal(
            $"while evaluating dotCall .take of {receiverName}",
            dottedContext.ErrorContext.ToString());
        Assert.IsType<EvalError.ArityMismatch>(dottedContext.Inner);
        Assert.Equal(
            "Callable `take(collection, count)` expects 2 arguments, but was called with 1 argument.",
            KatLangError.FromEvalError(dotted.Error).Message);
        Assert.Equal(1, dottedObservations.CallDiagnosticNameRenderCount);
    }

    [Fact]
    public void ResourceLimitError_DoesNotRenderCompoundCalleeName()
    {
        var observations = new EvaluationObservations();
        var (result, _) = Evaluator.RunCountedObserved(
            SuccessfulComplexCalleeCall(joinCount: 50),
            limits: new EvaluationLimits { MaxCollectionItems = 1 },
            observations: observations);

        Assert.True(result.IsError);
        Assert.True(result.Error.IsResourceLimit);
        Assert.Equal(0, observations.CallDiagnosticNameRenderCount);
    }

    [Fact]
    public void SuccessfulComplexCallee_CallHeavyAllocationMeasurement()
    {
        const int iterations = 2_000;
        var call = SuccessfulComplexCalleeCall(joinCount: 50);

        // Warm the exact path before measuring. This is an informational focused
        // measurement, not a permanent machine-dependent allocation ceiling.
        for (var i = 0; i < 20; i++)
            Assert.False(Evaluator.Run(call).IsError);

        GC.Collect();
        GC.WaitForPendingFinalizers();
        GC.Collect();
        var before = GC.GetAllocatedBytesForCurrentThread();
        for (var i = 0; i < iterations; i++)
            Assert.False(Evaluator.Run(call).IsError);
        var allocated = GC.GetAllocatedBytesForCurrentThread() - before;

        Console.WriteLine(
            $"successful-complex-callee allocation: {allocated} bytes / {iterations} calls "
            + $"({allocated / (double)iterations:F1} bytes/call)");
    }

    private static Expr SuccessfulComplexCalleeCall(int joinCount)
    {
        var receiver = JoinChain(joinCount);
        var callableDotExpression = new Expr.DotCall(receiver, "count", null);
        return new Expr.Call(callableDotExpression, OutputBundle.Empty);
    }

    private static OutputBundle Arguments(params Expr[] expressions)
        => expressions;

}
