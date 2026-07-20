namespace KatLang.Tests;

/// <summary>
/// Regression coverage for the parser recursion-depth budget (see
/// <c>Parser.MaxNestingDepth</c>), added after the Phase-2 depth-probe campaign found
/// that deeply nested surface input drove the recursive-descent parser into a fatal,
/// host-terminating stack overflow at inputs as small as ~330 bytes.
///
/// Every input below that previously crashed the process is now bounded, so it is safe
/// to run these directly in-process: the parse aborts at the budget (well below any
/// native stack boundary) and returns a structured diagnostic. A test completing at all
/// is itself the proof that the input no longer overflows the stack.
/// </summary>
public class ParserNestingDepthTests
{
    private const string NestingMessage = "Nesting is too deep";

    private static string Rep(string s, int n) => string.Concat(Enumerable.Repeat(s, n));

    private static bool HasNestingDiagnostic(SyntaxParseResult r)
        => r.Diagnostics.Any(d => d.Message.Contains(NestingMessage, StringComparison.Ordinal));

    private static Expr SingleOutput(SyntaxParseResult result)
    {
        var user = Assert.IsType<Algorithm.User>(result.Root);
        return Assert.Single(user.Output);
    }

    // ── Realistic deep input still succeeds (comfortably within budget) ───────
    [Theory]
    [InlineData("(", ")")]
    [InlineData("[", "]")]
    [InlineData("{", "}")]
    public void DeepBalanced_InBudget_ParsesWithoutError(string open, string close)
    {
        // 200 nested structural levels — above the 256-boundary bar's per-kind depth,
        // well below the ~289 structural budget, and far below the native crash.
        var result = Parser.ParseSyntax(Rep(open, 200) + "1" + Rep(close, 200));
        Assert.False(result.HasErrors);
        Assert.False(HasNestingDiagnostic(result));
    }

    [Theory]
    [InlineData("not ")]     // prefix not-chain (~1 counter/level)
    [InlineData("-")]        // prefix minus-chain
    public void DeepPrefix_InBudget_ParsesWithoutError(string prefix)
    {
        var result = Parser.ParseSyntax(Rep(prefix, 400) + "1");
        Assert.False(result.HasErrors);
        Assert.False(HasNestingDiagnostic(result));
    }

    // ── Boundary behaviour: just below parses, above diagnoses (no crash) ─────
    [Fact]
    public void StructuralBoundary_BelowParses_AboveDiagnoses()
    {
        // Effective structural limit is ~289 nested delimiters at MaxNestingDepth=580.
        // Margins keep this robust to small frame-count shifts.
        Assert.False(HasNestingDiagnostic(Parser.ParseSyntax(Rep("(", 260) + "1" + Rep(")", 260))));
        Assert.True(HasNestingDiagnostic(Parser.ParseSyntax(Rep("(", 340) + "1" + Rep(")", 340))));
    }

    // ── Over budget: one structured, source-positioned diagnostic, no crash ───
    [Theory]
    [InlineData("(", ")")]
    [InlineData("[", "]")]
    [InlineData("{", "}")]
    public void DeepBalanced_OverBudget_EmitsNestingDiagnostic(string open, string close)
    {
        var result = Parser.ParseSyntax(Rep(open, 5000) + "1" + Rep(close, 5000));
        Assert.True(result.HasErrors);
        Assert.True(HasNestingDiagnostic(result));
    }

    [Fact]
    public void DeepUnaryMinus_OverBudget_EmitsNestingDiagnostic()
        => Assert.True(HasNestingDiagnostic(Parser.ParseSyntax(Rep("-", 5000) + "1")));

    [Fact]
    public void DeepPower_OverBudget_EmitsNestingDiagnostic()
        => Assert.True(HasNestingDiagnostic(Parser.ParseSyntax(Rep("1 ^ ", 5000) + "1")));

    [Fact]
    public void DeepPattern_OverBudget_EmitsNestingDiagnostic()
        => Assert.True(HasNestingDiagnostic(
            Parser.ParseSyntax("F" + Rep("(", 5000) + "x" + Rep(")", 5000) + " = x\nF(1)")));

    // ── Malformed deep input recovers with a diagnostic (no crash) ────────────
    [Theory]
    [InlineData("(")]
    [InlineData("[")]
    [InlineData("{")]
    public void DeepUnclosed_OverBudget_RecoversWithoutCrash(string open)
    {
        var result = Parser.ParseSyntax(Rep(open, 5000) + "1");
        Assert.True(result.HasErrors);
    }

    [Fact]
    public void NestingDiagnostic_IsSourcePositioned()
    {
        var result = Parser.ParseSyntax(Rep("(", 5000) + "1" + Rep(")", 5000));
        var diagnostic = result.Diagnostics.First(d => d.Message.Contains(NestingMessage, StringComparison.Ordinal));
        Assert.True(diagnostic.Span.StartLineNumber >= 1);
        Assert.True(diagnostic.Span.StartColumn >= 1);
        Assert.True(diagnostic.Span.EndLineNumber >= diagnostic.Span.StartLineNumber);
    }

    // ── Semantics preserved for in-budget programs ────────────────────────────
    [Fact]
    public void Power_StaysRightAssociative()
    {
        // 1 ^ 2 ^ 3  ==  1 ^ (2 ^ 3)
        var outer = Assert.IsType<Expr.Binary>(SingleOutput(Parser.ParseSyntax("1 ^ 2 ^ 3")));
        Assert.Equal(BinaryOp.Pow, outer.Op);
        Assert.Equal(1m, Assert.IsType<Expr.Num>(outer.Left).Value);
        var inner = Assert.IsType<Expr.Binary>(outer.Right);
        Assert.Equal(BinaryOp.Pow, inner.Op);
        Assert.Equal(2m, Assert.IsType<Expr.Num>(inner.Left).Value);
        Assert.Equal(3m, Assert.IsType<Expr.Num>(inner.Right).Value);
    }

    [Fact]
    public void ShallowUnaryChain_ShapeUnchanged()
    {
        // ---1  ==  Unary(-, Unary(-, Unary(-, 1)))
        var u1 = Assert.IsType<Expr.Unary>(SingleOutput(Parser.ParseSyntax("---1")));
        Assert.Equal(UnaryOp.Minus, u1.Op);
        var u2 = Assert.IsType<Expr.Unary>(u1.Operand);
        var u3 = Assert.IsType<Expr.Unary>(u2.Operand);
        Assert.Equal(1m, Assert.IsType<Expr.Num>(u3.Operand).Value);
    }

    [Fact]
    public void ListParenScalar_StayDistinct()
    {
        Assert.IsType<Expr.ListLiteral>(SingleOutput(Parser.ParseSyntax("[7]")));   // exact list
        Assert.IsType<Expr.Num>(SingleOutput(Parser.ParseSyntax("(7)")));           // unwrapped grouping
        Assert.IsType<Expr.Num>(SingleOutput(Parser.ParseSyntax("7")));             // scalar
    }

    // ── Surface parser never emits the internal SequenceConstruct node ────────
    [Theory]
    [InlineData("((((1))))")]
    [InlineData("[[[[1]]]]")]
    [InlineData("((((1")]            // malformed (unclosed)
    public void NoSequenceConstruct_ShallowAndMalformed(string source)
        => Assert.False(FindsSequenceConstruct(Parser.ParseSyntax(source).Root));

    [Fact]
    public void NoSequenceConstruct_OverBudgetPlaceholder()
        => Assert.False(FindsSequenceConstruct(
            Parser.ParseSyntax(Rep("(", 5000) + "1" + Rep(")", 5000)).Root));

    private static bool FindsSequenceConstruct(Algorithm root)
    {
        var detector = new SequenceConstructDetector();
        detector.VisitAlgorithm(root);
        return detector.Found;
    }

    private sealed class SequenceConstructDetector : AstWalker
    {
        public bool Found { get; private set; }

        public override void VisitExpr(Expr expr)
        {
            if (expr is Expr.SequenceConstruct)
                Found = true;
            base.VisitExpr(expr);
        }
    }
}
