namespace KatLang.Tests;

/// <summary>
/// The ONE comparison precedence tier and first-class comparison chaining (September
/// 2026): all six comparison operators share one chainable level, unparenthesized
/// comparison operators at one syntactic level form ONE <see cref="Expr.Comparison"/>
/// node with adjacent-pair links (never nested binary comparisons), parentheses are
/// explicit expression boundaries that never merge into an outer chain, and every
/// already-settled precedence relationship around the tier is preserved. Lean twin of
/// the evaluation side: <c>lean/CoreTests/ComparisonChains.lean</c>; the semantic corpus
/// cases <c>comparison-chains-compare-adjacent-pairs</c> and
/// <c>comparison-chain-is-eager-after-false</c> tie the parsed chain AST to Lean.
/// </summary>
public class ComparisonChainParserTests
{
    private static Expr ParseSingleOutput(string source)
    {
        var result = Parser.ParseSyntax(source);
        Assert.False(result.HasErrors, string.Join("\n", result.Diagnostics.Select(d => d.Message)));
        return Assert.Single(result.Root.Output);
    }

    private static Expr.Comparison AssertChain(Expr expr, params ComparisonOp[] ops)
    {
        var chain = Assert.IsType<Expr.Comparison>(expr);
        Assert.Equal(ops, chain.Links.Select(link => link.Op));
        return chain;
    }

    private static IReadOnlyList<Expr> Operands(Expr.Comparison chain)
        => [chain.First, .. chain.Links.Select(link => link.Operand)];

    private static string Name(Expr expr) => Assert.IsType<Expr.Resolve>(expr).Name;

    /// <summary>
    /// A compact, precedence-revealing spelling of a parsed tree: every operator node is
    /// written in prefix form with its children in parentheses, so two different trees
    /// can never share a shape string.
    /// </summary>
    private static string Shape(Expr expr) => expr switch
    {
        Expr.Comparison chain => "cmp[" + string.Join(" ", chain.Links.Select(link => ExprNameRenderer.ComparisonOpText(link.Op)))
            + "](" + string.Join(", ", Operands(chain).Select(Shape)) + ")",
        Expr.Binary(var op, var left, var right) => $"{ExprNameRenderer.BinaryOpText(op)}({Shape(left)}, {Shape(right)})",
        Expr.Unary(UnaryOp.Not, var operand) => $"not({Shape(operand)})",
        Expr.Unary(_, var operand) => $"neg({Shape(operand)})",
        Expr.Index(var target, var selector) => $"index({Shape(target)}, {Shape(selector)})",
        Expr.Call(var function, var args) => $"call({Shape(function)}; {string.Join(", ", args.Select(Shape))})",
        Expr.DotCall dot => $"dot({Shape(dot.Target)}.{dot.Name})",
        Expr.Resolve(var name) => name,
        Expr.Num(var value) => value.ToString(System.Globalization.CultureInfo.InvariantCulture),
        Expr.BoolLiteral(var value) => value ? "true" : "false",
        _ => $"<{expr.GetType().Name}>",
    };

    // ── Chain structure: every operator class ───────────────────────────────

    [Theory]
    [InlineData("a < b < c", new[] { ComparisonOp.Lt, ComparisonOp.Lt })]
    [InlineData("a <= b >= c", new[] { ComparisonOp.Le, ComparisonOp.Ge })]
    [InlineData("a == b == c", new[] { ComparisonOp.Eq, ComparisonOp.Eq })]
    [InlineData("a != b != c", new[] { ComparisonOp.Ne, ComparisonOp.Ne })]
    [InlineData("a < b == c", new[] { ComparisonOp.Lt, ComparisonOp.Eq })]
    [InlineData("a == b < c", new[] { ComparisonOp.Eq, ComparisonOp.Lt })]
    [InlineData("a != b <= c", new[] { ComparisonOp.Ne, ComparisonOp.Le })]
    [InlineData("a > b != c", new[] { ComparisonOp.Gt, ComparisonOp.Ne })]
    public void ThreeOperandChains_AreOneNodeWithAdjacentLinks(string source, ComparisonOp[] ops)
    {
        var chain = AssertChain(ParseSingleOutput(source), ops);
        Assert.Equal(["a", "b", "c"], Operands(chain).Select(Name));
    }

    [Fact]
    public void FiveOperandMixedChain_KeepsEveryOperandOnceAndEveryOperatorInOrder()
    {
        // a < b <= c == d != e: the adjacent comparisons a < b, b <= c, c == d, d != e.
        var chain = AssertChain(
            ParseSingleOutput("a < b <= c == d != e"),
            ComparisonOp.Lt, ComparisonOp.Le, ComparisonOp.Eq, ComparisonOp.Ne);
        Assert.Equal(["a", "b", "c", "d", "e"], Operands(chain).Select(Name));
    }

    [Fact]
    public void EveryComparisonOperatorPair_FormsOneChain_NeverANestedComparison()
    {
        // The systematic contract behind "one tier": for EVERY ordered pair of the six
        // operators, `a OP1 b OP2 c` is one two-link chain — equality and ordering never
        // separate into `(a OP1 b) OP2 c` or `a OP1 (b OP2 c)`.
        var operators = Enum.GetValues<ComparisonOp>();
        foreach (var first in operators)
        {
            foreach (var second in operators)
            {
                var source = $"a {ExprNameRenderer.ComparisonOpText(first)} b {ExprNameRenderer.ComparisonOpText(second)} c";
                var chain = AssertChain(ParseSingleOutput(source), first, second);
                Assert.Equal(["a", "b", "c"], Operands(chain).Select(Name));
            }
        }
    }

    [Fact]
    public void ALongFlatChain_ParsesAsOneNode_AndCostsOneChainLevel()
    {
        // A chain is one flat node however many links it has: 300 links (more than the
        // chain-depth guard's 256 levels) stay inside the guard, which counts NESTING.
        var source = string.Join(" < ", Enumerable.Range(0, 301).Select(i => $"x{i}"));
        var chain = Assert.IsType<Expr.Comparison>(ParseSingleOutput(source));
        Assert.Equal(300, chain.Links.Count);
        Assert.All(chain.Links, link => Assert.Equal(ComparisonOp.Lt, link.Op));
        Assert.Equal("x0", Name(chain.First));
        Assert.Equal("x300", Name(chain.Links[^1].Operand));

        // ...and it costs exactly ONE level: the grouped chain plus 255 additions is the
        // 256-level maximum the guard admits, one more addition crosses it.
        static string Additions(string operand, int count) => "(" + operand + ")" + string.Concat(Enumerable.Repeat(" + 1", count));
        Assert.False(Parser.Parse(Additions(source, Parser.MaxExpressionChainDepth - 1)).HasErrors);
        var crossed = Parser.Parse(Additions(source, Parser.MaxExpressionChainDepth));
        Assert.Contains(crossed.Diagnostics, d => d.Code == DiagnosticCode.ExpressionChainTooDeep);
    }

    // ── Precedence interaction with the surrounding tiers ────────────────────

    [Theory]
    [InlineData("not a < b", "not(cmp[<](a, b))")]
    [InlineData("not a < b < c", "not(cmp[< <](a, b, c))")]
    [InlineData("not a == b != c", "not(cmp[== !=](a, b, c))")]
    [InlineData("a < b and c < d", "and(cmp[<](a, b), cmp[<](c, d))")]
    [InlineData("a < b xor c < d", "xor(cmp[<](a, b), cmp[<](c, d))")]
    [InlineData("a < b or c < d", "or(cmp[<](a, b), cmp[<](c, d))")]
    [InlineData("a < b < c and d", "and(cmp[< <](a, b, c), d)")]
    [InlineData("a and b < c < d", "and(a, cmp[< <](b, c, d))")]
    [InlineData("a + b < c * d", "cmp[<](+(a, b), *(c, d))")]
    [InlineData("-a ^ b < c", "cmp[<](neg(^(a, b)), c)")]
    [InlineData("a < b + c", "cmp[<](a, +(b, c))")]
    [InlineData("a < b + c < d", "cmp[< <](a, +(b, c), d)")]
    [InlineData("a * b == c mod d != e - f", "cmp[== !=](*(a, b), mod(c, d), -(e, f))")]
    [InlineData("a:0 < b.c < f(d)", "cmp[< <](index(a, 0), dot(b.c), call(f; d))")]
    [InlineData("not a < b and not c == d", "and(not(cmp[<](a, b)), not(cmp[==](c, d)))")]
    [InlineData("not not a < b", "not(not(cmp[<](a, b)))")]
    [InlineData("-a < -b", "cmp[<](neg(a), neg(b))")]
    [InlineData("a ^ b ^ c < d", "cmp[<](^(a, ^(b, c)), d)")]
    public void ComparisonChains_ComposeWithTheSurroundingPrecedenceTiers(string source, string expectedShape)
        => Assert.Equal(expectedShape, Shape(ParseSingleOutput(source)));

    /// <summary>
    /// The pairwise parser-precedence contract: for every ordered pair of operators from
    /// each tier, <c>a OP1 b OP2 c</c> parses to the tree the ladder prescribes —
    /// or &lt; xor &lt; and &lt; (one comparison tier) &lt; + &lt; * &lt; ^ — with left
    /// associativity everywhere except the right-associative <c>^</c> and the chaining
    /// comparison tier. A precedence change anywhere on the ladder fails a row here.
    /// </summary>
    public static TheoryData<string, string> OperatorPairs()
    {
        // One representative per tier plus the full comparison tier; (spelling, tier, shape head).
        (string Text, int Tier, string Head)[] operators =
        [
            ("or", 1, "or"), ("xor", 2, "xor"), ("and", 3, "and"),
            ("<", 5, "<"), ("<=", 5, "<="), (">", 5, ">"), (">=", 5, ">="), ("==", 5, "=="), ("!=", 5, "!="),
            ("+", 6, "+"), ("-", 6, "-"), ("*", 7, "*"), ("/", 7, "/"), ("div", 7, "div"), ("mod", 7, "mod"), ("^", 9, "^"),
        ];

        var data = new TheoryData<string, string>();
        foreach (var first in operators)
        {
            foreach (var second in operators)
            {
                var source = $"a {first.Text} b {second.Text} c";
                string expected;
                if (first.Tier == 5 && second.Tier == 5)
                    expected = $"cmp[{first.Head} {second.Head}](a, b, c)";
                else if (first.Tier < second.Tier || (first.Tier == second.Tier && first.Tier == 9))
                    expected = Node(first, "a", Node(second, "b", "c"));
                else
                    expected = Node(second, Node(first, "a", "b"), "c");
                data.Add(source, expected);
            }
        }

        return data;

        static string Node((string Text, int Tier, string Head) op, string left, string right)
            => op.Tier == 5 ? $"cmp[{op.Head}]({left}, {right})" : $"{op.Head}({left}, {right})";
    }

    [Theory]
    [MemberData(nameof(OperatorPairs))]
    public void PairwisePrecedenceContract_EveryOperatorPairParsesAsTheLadderPrescribes(string source, string expectedShape)
        => Assert.Equal(expectedShape, Shape(ParseSingleOutput(source)));

    // ── Parentheses are explicit expression boundaries ──────────────────────

    [Theory]
    [InlineData("(a < b) == true", "cmp[==](cmp[<](a, b), true)")]
    [InlineData("a < (b == c)", "cmp[<](a, cmp[==](b, c))")]
    [InlineData("(a < b) == (c < d)", "cmp[==](cmp[<](a, b), cmp[<](c, d))")]
    [InlineData("(a < b < c) == true", "cmp[==](cmp[< <](a, b, c), true)")]
    [InlineData("a == (b < c < d)", "cmp[==](a, cmp[< <](b, c, d))")]
    [InlineData("(a < b) < c", "cmp[<](cmp[<](a, b), c)")]
    [InlineData("a < (b < c)", "cmp[<](a, cmp[<](b, c))")]
    [InlineData("((a < b) == c) != d", "cmp[!=](cmp[==](cmp[<](a, b), c), d)")]
    [InlineData("(a < b) == c < d", "cmp[== <](cmp[<](a, b), c, d)")]
    [InlineData("a < b == (c < d)", "cmp[< ==](a, b, cmp[<](c, d))")]
    [InlineData("not (a < b) == c", "not(cmp[==](cmp[<](a, b), c))")]
    [InlineData("(not a) < b", "cmp[<](not(a), b)")]
    public void Parentheses_BreakChains_AndNeverMergeIntoTheOuterChain(string source, string expectedShape)
        => Assert.Equal(expectedShape, Shape(ParseSingleOutput(source)));

    [Fact]
    public void RedundantParentheses_AroundAWholeChain_LeaveOneChain()
    {
        // (a < b < c) is the same tree as the bare chain, re-spanned to the group (F6).
        var chain = AssertChain(ParseSingleOutput("(a < b < c)"), ComparisonOp.Lt, ComparisonOp.Lt);
        Assert.Equal(["a", "b", "c"], Operands(chain).Select(Name));
        Assert.Equal(new SourceSpan(1, 1, 1, 12), chain.Span);
    }

    // ── Spans ────────────────────────────────────────────────────────────────

    [Fact]
    public void ChainSpans_CoverTheWholeChain_AndEachOperandItsOwnText()
    {
        var chain = AssertChain(ParseSingleOutput("ab < cd <= ef"), ComparisonOp.Lt, ComparisonOp.Le);
        Assert.Equal(new SourceSpan(1, 1, 1, 14), chain.Span);
        Assert.Equal(new SourceSpan(1, 1, 1, 3), chain.First.Span);
        Assert.Equal(new SourceSpan(1, 6, 1, 8), chain.Links[0].Operand.Span);
        Assert.Equal(new SourceSpan(1, 12, 1, 14), chain.Links[1].Operand.Span);

        // A parenthesized first operand keeps the group's full extent (F6), so a link
        // that fails at evaluation is located at its two operands' hull.
        var grouped = AssertChain(ParseSingleOutput("(a < b) == c"), ComparisonOp.Eq);
        Assert.Equal(new SourceSpan(1, 1, 1, 13), grouped.Span);
        Assert.Equal(new SourceSpan(1, 1, 1, 8), grouped.First.Span);
        Assert.Equal(new SourceSpan(1, 12, 1, 13), grouped.Links[0].Operand.Span);

        // A multi-line chain (trailing operators continue) spans both lines.
        var multiline = AssertChain(ParseSingleOutput("a <\n  b <\n  c"), ComparisonOp.Lt, ComparisonOp.Lt);
        Assert.Equal(new SourceSpan(1, 1, 3, 4), multiline.Span);
    }

    // ── Line rules ───────────────────────────────────────────────────────────

    [Fact]
    public void ComparisonOperators_FollowTheBinaryOperatorLineRule()
    {
        // A trailing comparison operator continues onto the next line.
        AssertChain(ParseSingleOutput("a <\nb"), ComparisonOp.Lt);
        AssertChain(ParseSingleOutput("a < b ==\nc"), ComparisonOp.Lt, ComparisonOp.Eq);

        // A comparison-led line never continues the previous row: the first row is a
        // closed one-link chain and the dangling operator is an ordinary error.
        var broken = Parser.ParseSyntax("a < b\n< c");
        Assert.True(broken.HasErrors);
        AssertChain(broken.Root.Output[0], ComparisonOp.Lt);
    }

    // ── Malformed input never recovers into a different valid chain ─────────

    [Theory]
    [InlineData("a < < b")]
    [InlineData("a == != b")]
    [InlineData("a < b <")]
    [InlineData("< a < b")]
    public void MalformedChains_AreDiagnosed(string source)
        => Assert.True(Parser.ParseSyntax(source).HasErrors);

    [Fact]
    public void MissingOperand_RecoversWithAPlaceholder_NotBySkippingTheLink()
    {
        // `a < < b`: the missing operand after the first `<` is a recovery placeholder,
        // so the diagnosed tree can never silently read as the valid chain `a < b` —
        // the first row is `a < <placeholder>` and `b` is left to the next row.
        var result = Parser.ParseSyntax("a < < b");
        Assert.True(result.HasErrors);
        var chain = AssertChain(result.Root.Output[0], ComparisonOp.Lt);
        Assert.Equal("a", Name(chain.First));
        Assert.IsType<Expr.Num>(chain.Links[0].Operand);
        Assert.DoesNotContain(result.Root.Output, row => row is Expr.Comparison { Links: [{ Operand: Expr.Resolve { Name: "b" } }] });
    }

    [Fact]
    public void SpreadOperands_AreRejectedInEveryChainPosition_AndUnwrapped()
    {
        foreach (var source in new[] { "A* < B < C", "A < B* < C", "A < B < C*" })
        {
            var result = Parser.ParseSyntax(source);
            var diagnostic = Assert.Single(result.Diagnostics);
            Assert.Equal(DiagnosticCode.MisplacedSpread, diagnostic.Code);
            var chain = AssertChain(Assert.Single(result.Root.Output), ComparisonOp.Lt, ComparisonOp.Lt);
            Assert.Equal(["A", "B", "C"], Operands(chain).Select(Name));
        }
    }

    [Fact]
    public void SpreadOperands_OnBothSidesOfOneLink_AreReportedInWrittenOrder()
    {
        var result = Parser.ParseSyntax("A* < B*");
        Assert.Equal(2, result.Diagnostics.Count);
        Assert.All(result.Diagnostics, d => Assert.Equal(DiagnosticCode.MisplacedSpread, d.Code));
        Assert.Equal(new SourceSpan(1, 1, 1, 3), result.Diagnostics[0].Span);
        Assert.Equal(new SourceSpan(1, 6, 1, 8), result.Diagnostics[1].Span);
    }

    [Theory]
    [InlineData("a < not b", 5, "cmp[<](a, not(b))")]
    [InlineData("a < b == not c", 10, "cmp[< ==](a, b, not(c))")]
    // The recovery parses the negation AS IF PARENTHESIZED at `not`'s own tier, so the
    // negation absorbs the rest of the chain to its right (`a < (not b == c)` is
    // `a < (not (b == c))`, exactly like the established `1 + not x > 3` recovery).
    [InlineData("a < not b == c", 5, "cmp[<](a, not(cmp[==](b, c)))")]
    public void MisplacedNotInsideAChain_IsDiagnosedAtTheKeyword_AndRecoveredAsAParenthesizedOperand(string source, int column, string recoveredShape)
    {
        var result = Parser.ParseSyntax(source);
        var diagnostic = Assert.Single(result.Diagnostics);
        Assert.Equal(DiagnosticCode.UnexpectedToken, diagnostic.Code);
        Assert.Equal(new SourceSpan(1, column, 1, column + 3), diagnostic.Span);
        // The recovery is the tree `(not …)` would parse to: the negation is one operand
        // of the chain, never a negation of the whole chain.
        Assert.Equal(recoveredShape, Shape(Assert.Single(result.Root.Output)));
    }

    [Fact]
    public void AChain_IsNotAnOpenForm()
    {
        var result = Parser.ParseSyntax("open a < b");
        Assert.True(result.HasErrors);
        Assert.Contains(result.Diagnostics, d => d.Code == DiagnosticCode.BadOpenForm && d.Message.Contains("comparison", StringComparison.Ordinal));
    }

    // ── The elaborated front end keeps the chain shape ───────────────────────

    [Fact]
    public void Elaboration_KeepsTheChain_AndInfersImplicitParametersInChainOrder()
    {
        var parsed = SourceProvenance.ParseValid("InRange = low < x <= high");
        var property = Assert.Single(parsed.Root.Properties);
        var algorithm = Assert.IsType<Algorithm.User>(property.Value);
        Assert.Equal(["low", "x", "high"], algorithm.Params);
        var chain = AssertChain(Assert.Single(algorithm.Output), ComparisonOp.Lt, ComparisonOp.Le);
        Assert.All(Operands(chain), operand => Assert.IsType<Expr.Param>(operand));
    }
}
