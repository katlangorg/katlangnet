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

    private static bool HasExpressionChainDiagnostic(SyntaxParseResult r)
        => r.Diagnostics.Any(
            d => d.Message.Contains("Expression operator or postfix chain is too deep", StringComparison.Ordinal));

    private static void AssertParses(string source)
    {
        var result = Parser.ParseSyntax(source);
        Assert.False(result.HasErrors, string.Join(Environment.NewLine, result.Diagnostics));
        Assert.False(HasNestingDiagnostic(result));
    }

    private static Expr SingleOutput(SyntaxParseResult result)
    {
        var user = Assert.IsType<Algorithm.User>(result.Root);
        return Assert.Single(user.Output);
    }

    // ── Realistic deep input still succeeds (comfortably within budget) ───────
    [Theory]
    [InlineData("(", ")", 90)]   // groups: 4 weighted units/level (heavy machinery)
    [InlineData("{", "}", 90)]   // blocks: 4 units/level
    [InlineData("[", "]", 120)]  // lists: 3 units/level
    public void DeepBalanced_InBudget_ParsesWithoutError(string open, string close, int levels)
    {
        // Just under each shape's budget capacity — every capacity was proven to
        // parse on a dedicated 512 KiB thread (half the documented 1 MiB minimum),
        // so the budget, not the machine, is what stops deeper input.
        var result = Parser.ParseSyntax(Rep(open, levels) + "1" + Rep(close, levels));
        Assert.False(result.HasErrors);
        Assert.False(HasNestingDiagnostic(result));
    }

    [Theory]
    [InlineData("not ")]     // prefix not-chain (~1 weighted unit/level)
    [InlineData("-")]        // prefix minus-chain
    public void DeepPrefix_InBudget_ParsesWithoutError(string prefix)
    {
        var result = Parser.ParseSyntax(Rep(prefix, 350) + "1");
        Assert.False(result.HasErrors);
        Assert.False(HasNestingDiagnostic(result));
    }

    // ── Boundary behaviour: exact per-shape maxima parse, one beyond diagnoses ─
    [Theory]
    [InlineData("(", ")", 95)]   // 95 x 4 units + 2 = 382 <= 384; 96 x 4 + 2 = 386
    [InlineData("{", "}", 95)]
    [InlineData("[", "]", 127)]  // 127 x 3 + 2 = 383 <= 384
    public void StructuralBoundary_AtMaximumParses_OneBeyondDiagnoses(string open, string close, int max)
    {
        AssertParses(Rep(open, max) + "1" + Rep(close, max));
        Assert.True(HasNestingDiagnostic(Parser.ParseSyntax(Rep(open, max + 1) + "1" + Rep(close, max + 1))));
    }

    [Fact]
    public void PrefixBoundary_AtMaximumParses_OneBeyondDiagnoses()
    {
        // Unary levels charge one unit each: 382 + entry = 384 units exactly.
        AssertParses(Rep("-", 382) + "1");
        Assert.True(HasNestingDiagnostic(Parser.ParseSyntax(Rep("-", 383) + "1")));
    }

    [Fact]
    public void PowerBoundary_UsesTheEstablishedExpressionChainMaximum()
    {
        // Power is parsed right-associatively and charges the cumulative recursion
        // counter, but its completed AST is also an operator chain. The established
        // 256-link chain policy is therefore the first successful-surface boundary.
        // (ParsePower deliberately holds ONE live unit per `^` level — the
        // exponent re-enters ParseUnary under the still-live entry charge — so
        // this boundary is unchanged by the power-vs-unary precedence split.)
        AssertParses(Rep("1 ^ ", Parser.MaxExpressionChainDepth) + "1");
        var oneBeyond = Parser.ParseSyntax(Rep("1 ^ ", Parser.MaxExpressionChainDepth + 1) + "1");
        Assert.True(oneBeyond.HasErrors);
        Assert.True(HasExpressionChainDiagnostic(oneBeyond));
        Assert.False(HasNestingDiagnostic(oneBeyond));
    }

    [Fact]
    public void AlternatingUnaryPowerBoundary_AtMaximumParses_OneBeyondDiagnoses()
    {
        // Under power-over-unary precedence, `-1 ^ -1 ^ ... ^ 1` nests as
        // `-(1 ^ (-(1 ^ ...)))`: each `-1 ^ ` segment holds TWO live units
        // (the prefix ParseUnary level plus the exponent's re-entered
        // ParseUnary level), and the chain guard never accumulates through the
        // interleaved unary wrappers, so the recursion budget is the first
        // boundary for this compound shape. Entry and the final operand add
        // two more units: 2N + 2 <= 384 admits N <= 191 segments.
        AssertParses(Rep("-1 ^ ", 191) + "1");
        Assert.True(HasNestingDiagnostic(Parser.ParseSyntax(Rep("-1 ^ ", 192) + "1")));
    }

    [Fact]
    public void AlternatingUnaryPower_OverBudget_EmitsNestingDiagnostic()
        => Assert.True(HasNestingDiagnostic(Parser.ParseSyntax(Rep("-1 ^ ", 5000) + "1")));

    [Fact]
    public void DeepUnaryExponentTail_OverBudget_EmitsNestingDiagnostic()
        => Assert.True(HasNestingDiagnostic(Parser.ParseSyntax("2 ^ " + Rep("-", 5000) + "1")));

    [Fact]
    public void CallNestingBoundary_AtMaximumParses_OneBeyondDiagnoses()
    {
        // Call argument levels charge 3 units (base 2 + call surcharge 1).
        AssertParses("f(x) = x\n" + Rep("f(", 127) + "1" + Rep(")", 127));
        Assert.True(HasNestingDiagnostic(Parser.ParseSyntax(
            "f(x) = x\n" + Rep("f(", 128) + "1" + Rep(")", 128))));
    }

    [Fact]
    public void PatternBoundary_AtMaximumParses_OneBeyondDiagnoses()
    {
        AssertParses("F" + Rep("(", 384) + "x" + Rep(")", 384) + " = x\nF(1)");
        Assert.True(HasNestingDiagnostic(Parser.ParseSyntax(
            "F" + Rep("(", 385) + "x" + Rep(")", 385) + " = x\nF(1)")));
    }

    [Fact]
    public void MixedContainers_ChargeCumulatively_NeverPerMechanism()
    {
        // The one cumulative budget is shared by every grammar mechanism: alternating
        // group/list/block levels charge 4 + 3 + 4 units per cycle, so ~35 cycles
        // exhaust it even though each DELIMITER KIND alone is far below its own
        // capacity — per-mechanism budgets would wrongly admit this shape.
        AssertParses(Rep("([{", 34) + "1" + Rep("}])", 34));
        Assert.True(HasNestingDiagnostic(Parser.ParseSyntax(Rep("([{", 35) + "1" + Rep("}])", 35))));
    }

    [Fact]
    public void InitialDebt_IsBoundedAndComposesWithExpressionFrames()
    {
        AssertParsesWithDebt("1", 382);

        var oneBeyond = Parser.ParseSyntax("1", 383);
        Assert.True(oneBeyond.HasErrors);
        Assert.Single(oneBeyond.Diagnostics, d => d.Message.Contains(NestingMessage, StringComparison.Ordinal));

        var hostileDebt = Parser.ParseSyntax("1", int.MaxValue);
        Assert.True(hostileDebt.HasErrors);
        Assert.Single(hostileDebt.Diagnostics, d => d.Message.Contains(NestingMessage, StringComparison.Ordinal));

        static void AssertParsesWithDebt(string source, int debt)
        {
            var result = Parser.ParseSyntax(source, debt);
            Assert.False(result.HasErrors, string.Join(Environment.NewLine, result.Diagnostics));
        }
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
        => Assert.False(FindsSequenceConstruct(SourceProvenance.ParseSyntaxAllowingDiagnosticsRoot(source)));

    [Fact]
    public void NoSequenceConstruct_OverBudgetPlaceholder()
        => Assert.False(FindsSequenceConstruct(
            SourceProvenance.ParseSyntaxAllowingDiagnosticsRoot(Rep("(", 5000) + "1" + Rep(")", 5000))));

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
