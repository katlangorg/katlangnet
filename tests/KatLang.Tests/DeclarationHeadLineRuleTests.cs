namespace KatLang.Tests;

/// <summary>
/// F7 — the declaration-head line rule: a declaration head (`Name =`,
/// `Name(pattern) =`, `x, *y, z =`, `~Name =`, `public Name =`) is written on ONE
/// physical line. A physical newline never assembles a head implicitly, so a name,
/// call, group, or expression list on one line never retroactively becomes a
/// clause, property, or deconstruction head because declaration syntax appears on
/// the next line: the first line stays the closed output row it is and the stray
/// `=` is the one reported error. Explicit continuation AFTER a recognized head —
/// the body of `A =` or `Foo(x) =` on the next line, a pattern list inside an
/// already-open clause-head `( … )` — is unaffected, exactly like the operand of a
/// trailing binary operator, and so is the member after a trailing `.`.
/// </summary>
public class DeclarationHeadLineRuleTests
{
    private const string HeadLineRuleFragment = "A declaration head cannot be assembled across a physical newline";

    private static string Display(string source)
    {
        var result = KatLangEngine.Run(source);
        Assert.True(result is RunResult.Success, $"Expected success but got: {result.ToDisplayString()}");
        return result.ToDisplayString().Replace("\r\n", "\n");
    }

    /// <summary>
    /// The raw parser reports exactly one diagnostic — the stray '=' with the line-rule
    /// repair — at the given position, and the full front end agrees (no elaboration
    /// pass invents a declaration behind the parser's back).
    /// </summary>
    private static SyntaxParseResult AssertRejectedAtStrayEquals(string source, int line, int column)
    {
        var raw = Parser.ParseSyntax(source);
        Assert.True(raw.HasErrors, $"expected the stray-'=' diagnostic for:{Environment.NewLine}{source}");
        var diagnostic = Assert.Single(raw.Diagnostics);
        Assert.Equal(DiagnosticCode.UnexpectedToken, diagnostic.Code);
        Assert.Contains(HeadLineRuleFragment, diagnostic.Message, StringComparison.Ordinal);
        Assert.Equal(new SourceSpan(line, column, line, column + 1), diagnostic.Span);   // the one-character `=`

        var elaborated = Parser.Parse(source);
        Assert.True(elaborated.HasErrors);
        Assert.Contains(
            elaborated.Diagnostics,
            d => d.Code == DiagnosticCode.UnexpectedToken && d.Message.Contains(HeadLineRuleFragment, StringComparison.Ordinal));
        return raw;
    }

    // ── Rejected: heads never span the physical newline ─────────────────────

    [Theory]
    [InlineData("\n")]
    [InlineData("\r\n")]
    public void NameThenParameterListOnTheNextLine_IsNotAClauseHead(string newline)
    {
        // Before the rule `Foo` newline `(x) = x + 1` silently parsed as the clause
        // `Foo(x) = x + 1`. Now `Foo` is an output row, `(x)` the next row, and the
        // `=` is stray; no property is declared.
        var raw = AssertRejectedAtStrayEquals(string.Join(newline, "Foo", "(x) = x + 1", "Foo(1)"), 2, 5);

        Assert.Empty(raw.Root.Properties);
        Assert.Equal("Foo", Assert.IsType<Expr.Resolve>(raw.Root.Output[0]).Name);
        // The grouped row `(x)` is the name `x` itself (parentheses group syntax).
        Assert.Equal("x", Assert.IsType<Expr.Resolve>(raw.Root.Output[1]).Name);
    }

    [Theory]
    [InlineData("\n")]
    [InlineData("\r\n")]
    public void NameThenEqualsOnTheNextLine_IsNotAPropertyHead(string newline)
    {
        var raw = AssertRejectedAtStrayEquals(string.Join(newline, "A", "= 1", "A"), 2, 1);

        Assert.Empty(raw.Root.Properties);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(raw.Root.Output[0]).Name);
    }

    [Theory]
    [InlineData("Foo # a comment\n(x) = x + 1", 2, 5)]
    [InlineData("A # a comment\n= 1", 2, 1)]
    [InlineData("A\n# a comment line\n= 1", 3, 1)]
    [InlineData("A\n\n= 1", 3, 1)]
    public void CommentsAndBlankLinesAtTheBoundary_NeverRelaxTheRule(string source, int line, int column)
        => AssertRejectedAtStrayEquals(source, line, column);

    [Theory]
    [InlineData("Foo\n    (x) = x + 1", 2, 9)]
    [InlineData("A\n    = 1", 2, 5)]
    [InlineData("A\n\t= 1", 2, 2)]
    public void Indentation_NeverRelaxesTheRule(string source, int line, int column)
        => AssertRejectedAtStrayEquals(source, line, column);

    [Fact]
    public void CallThenEqualsOnTheNextLine_IsNotAClauseHead()
    {
        // `Foo(x)` is a closed call row; `= x + 1` on the next line never turns it
        // into the clause `Foo(x) = x + 1`. Before the rule it silently did — and
        // `Foo(1)` newline `= 3` even added a SECOND clause to an existing family,
        // so the program printed nothing at all.
        AssertRejectedAtStrayEquals("Foo(x)\n= x + 1\nFoo(1)", 2, 1);

        var raw = AssertRejectedAtStrayEquals("Foo(x) = x\nFoo(1)\n= 3", 3, 1);
        var family = Assert.Single(raw.Root.Properties);
        Assert.Equal("Foo", family.Name);
        Assert.IsType<Algorithm.User>(family.Value); // one clause, never a conditional family
        var call = Assert.IsType<Expr.Call>(raw.Root.Output[0]);
        Assert.Equal("Foo", Assert.IsType<Expr.Resolve>(call.Function).Name);
    }

    [Fact]
    public void ExpressionListThenEqualsOnTheNextLine_IsNotADeconstructionHead()
    {
        var raw = AssertRejectedAtStrayEquals("x, y\n= 1, 2\nx, y", 2, 1);

        Assert.Empty(raw.Root.Properties);
        Assert.Equal("x", Assert.IsType<Expr.Resolve>(raw.Root.Output[0]).Name);
        Assert.Equal("y", Assert.IsType<Expr.Resolve>(raw.Root.Output[1]).Name);
    }

    [Fact]
    public void TrailingCommaThenDeclarationOnTheNextLine_DoesNotAssembleADeconstructionHead()
    {
        // `x,` never becomes the first target of a two-line `x, y = 1, 2` head. The
        // next line is a complete one-line head of its own (`y = 1, 2`), and a
        // declaration head is never an expression-list slot (#9): the dangling comma is
        // the one error, and `y` stays the property that line declares.
        var raw = Parser.ParseSyntax("x,\ny = 1, 2");
        var diagnostic = Assert.Single(raw.Diagnostics);
        Assert.Equal(DiagnosticCode.UnexpectedToken, diagnostic.Code);
        Assert.Equal(new SourceSpan(1, 2, 1, 3), diagnostic.Span); // the dangling ','
        Assert.DoesNotContain(HeadLineRuleFragment, diagnostic.Message, StringComparison.Ordinal);
        var y = Assert.Single(raw.Root.Properties);
        Assert.Equal("y", y.Name);
        Assert.Equal(2, y.Value.Output.Count); // the ordinary property `y = 1, 2`, no deconstruction
        Assert.Equal("x", Assert.IsType<Expr.Resolve>(raw.Root.Output[0]).Name);
    }

    [Fact]
    public void PublicOnItsOwnLine_DoesNotAssembleAPublicHead()
    {
        var raw = Parser.ParseSyntax("public\nName = 1\nName");

        var diagnostic = Assert.Single(raw.Diagnostics);
        Assert.Equal(DiagnosticCode.UnexpectedToken, diagnostic.Code);
        Assert.Equal(new SourceSpan(1, 1, 1, 7), diagnostic.Span);
        var property = Assert.Single(raw.Root.Properties);
        Assert.Equal("Name", property.Name);
        Assert.False(property.IsPublic);
    }

    [Fact]
    public void GracedNameThenEqualsOnTheNextLine_IsAPrefixGraceRowNotAPropertyHead()
    {
        // `~q` on its own line is a prefix-grace output row; the `=` on the next
        // line is stray (before the rule the pair was the invalid-grace property
        // head `~q = 1`).
        var raw = Parser.ParseSyntax("~q\n= 1");

        var diagnostic = Assert.Single(raw.Diagnostics);
        Assert.Equal(DiagnosticCode.UnexpectedToken, diagnostic.Code);
        Assert.Equal(new SourceSpan(2, 1, 2, 2), diagnostic.Span);
        var grace = Assert.IsType<Expr.Grace>(raw.Root.Output[0]);
        Assert.Equal("q", Assert.IsType<Expr.Resolve>(grace.Inner).Name);
        Assert.Empty(raw.Root.Properties);
    }

    [Fact]
    public void InsideABraceBody_TheRuleIsTheSame()
    {
        var raw = Parser.ParseSyntax("Q = {\n    Foo\n    (x) = x + 1\n}\nQ");

        var diagnostic = Assert.Single(raw.Diagnostics);
        Assert.Equal(DiagnosticCode.UnexpectedToken, diagnostic.Code);
        Assert.Contains(HeadLineRuleFragment, diagnostic.Message, StringComparison.Ordinal);
        Assert.Equal(new SourceSpan(3, 9, 3, 10), diagnostic.Span);
        var q = Assert.Single(raw.Root.Properties).Value;
        Assert.Empty(q.Properties);
        Assert.Equal("Foo", Assert.IsType<Expr.Resolve>(q.Output[0]).Name);
    }

    [Fact]
    public void DeclarationOnTheLineAfterEquals_IsNotABody()
    {
        // The body of `A =` may begin on the next line like a trailing operator's
        // operand, but a declaration head is never an operand or a body (#9): `B = 1`
        // stays B's declaration, and A's missing body is the one error, reported at
        // the dangling '=' — exactly like `A -` newline `B = 1`.
        var raw = Parser.ParseSyntax("A =\nB = 1");
        var diagnostic = Assert.Single(raw.Diagnostics);
        Assert.Equal(DiagnosticCode.UnexpectedToken, diagnostic.Code);
        Assert.Equal(new SourceSpan(1, 3, 1, 4), diagnostic.Span); // A's '='
        Assert.Equal(new[] { "A", "B" }, raw.Root.Properties.Select(p => p.Name));
        Assert.IsType<Expr.Num>(Assert.Single(raw.Root.Properties[0].Value.Output)); // the missing body's placeholder
        Assert.Equal(1, Assert.IsType<Expr.Num>(Assert.Single(raw.Root.Properties[1].Value.Output)).Value);

        var minus = Parser.ParseSyntax("A = 1 -\nB = 1");
        Assert.Equal(new SourceSpan(1, 7, 1, 8), Assert.Single(minus.Diagnostics).Span); // the dangling '-'
        Assert.Equal(new[] { "A", "B" }, minus.Root.Properties.Select(p => p.Name));
    }

    // ── Retained: explicit continuation after a recognized head ─────────────

    [Theory]
    [InlineData("A =\n1\nA", "1")]
    [InlineData("A =\r\n1\r\nA", "1")]
    [InlineData("A = # note\n1\nA", "1")]
    [InlineData("Foo(x) =\nx + 1\nFoo(1)", "2")]
    [InlineData("F(a,\nb) = a + b\nF(1, 2)", "3")]
    [InlineData("F(a\n) = a\nF(1)", "1")]
    [InlineData("a = 5\nb(x) = x + 1\na.\nb", "6")]
    [InlineData("P = a.\nb\nb(x) = x + 1\nP(5)", "6")]
    public void ExplicitContinuationAfterARecognizedHead_StaysLegal(string source, string expected)
    {
        Assert.False(Parser.Parse(source).HasErrors);
        Assert.Equal(expected, Display(source));
    }

    [Fact]
    public void BodyOnTheLineAfterEquals_IsTheDeclaredBody()
    {
        var raw = Parser.ParseSyntax("A =\n1");
        Assert.False(raw.HasErrors);
        var a = Assert.Single(raw.Root.Properties);
        Assert.Equal(1, Assert.IsType<Expr.Num>(Assert.Single(a.Value.Output)).Value);
        Assert.Empty(raw.Root.Output);

        var clause = Parser.ParseSyntax("Foo(x) =\nx + 1");
        Assert.False(clause.HasErrors);
        var foo = Assert.Single(clause.Root.Properties);
        Assert.Equal("Foo", foo.Name);
        Assert.IsType<Expr.Binary>(Assert.Single(foo.Value.Output));
    }

    [Fact]
    public void PatternListInsideAnOpenClauseHead_MaySpanLines_ButTheHeadTokensMayNot()
    {
        // The `(` shares the name's line and the `=` shares the `)`'s line; the
        // pattern list between them is an already-open delimiter and spans lines.
        var raw = Parser.ParseSyntax("F(a,\n  b) = a + b");
        Assert.False(raw.HasErrors);
        Assert.Equal("F", Assert.Single(raw.Root.Properties).Name);

        AssertRejectedAtStrayEquals("F(a, b)\n= a + b", 2, 1);
    }

    [Fact]
    public void MemberOnTheLineAfterATrailingDot_IsTheDotEdge()
    {
        var raw = Parser.ParseSyntax("a.\nb");
        Assert.False(raw.HasErrors);
        var edge = Assert.IsType<Expr.DotCall>(Assert.Single(raw.Root.Output));
        Assert.Equal("b", edge.Name);
        Assert.Equal("a", Assert.IsType<Expr.Resolve>(edge.Target).Name);
    }

    [Theory]
    [InlineData("A", "= 1")]
    [InlineData("Foo", "(x) = x + 1")]
    [InlineData("Foo(x)", "= x + 1")]
    [InlineData("x, y", "= 1, 2")]
    [InlineData("~q", "= 1")]
    public void RejectedSplitHeads_PreserveLaterDeclarationsAndRows(string first, string second)
    {
        foreach (var newline in new[] { "\n", "\r\n" })
        foreach (var trivia in new[] { "", "  ", "\t", " # trailing", " # trailing" + newline + "# comment" + newline })
        foreach (var nested in new[] { false, true })
        {
            var body = first + trivia + newline + "\t" + second + newline + "Keep = 42" + newline + "Keep";
            var raw = Parser.ParseSyntax(nested ? "Box = {\n" + body + "\n}\nBox" : body);
            Assert.True(raw.HasErrors, body);
            var scope = nested ? Assert.Single(raw.Root.Properties).Value : raw.Root;
            Assert.Equal("Keep", Assert.Single(scope.Properties).Name);
            Assert.Equal("Keep", Assert.IsType<Expr.Resolve>(scope.Output[^1]).Name);
        }
    }

    [Theory]
    [InlineData("A*\nB = 2", true)]
    [InlineData("A*\nB\n= 2", false)]
    [InlineData("A*\nB(x) = x", true)]
    [InlineData("A*\nB(x)\n= x", false)]
    [InlineData("A*\nB\n(x) = x", false)]
    [InlineData("A*\nx, y = 1, 2", true)]
    [InlineData("A*\nx, y\n= 1, 2", false)]
    public void LineFinalStar_UsesOnlyAnActualDeclarationHead(string source, bool declaration)
    {
        foreach (var newline in new[] { "\n", "\r\n" })
        {
            var raw = Parser.ParseSyntax(source.Replace("\n", newline, StringComparison.Ordinal));
            if (declaration)
            {
                Assert.False(raw.HasErrors);
                Assert.IsType<Expr.SequenceSpread>(raw.Root.Output[0]);
                Assert.NotEmpty(raw.Root.Properties);
            }
            else
            {
                Assert.True(raw.HasErrors);
                Assert.Empty(raw.Root.Properties);
                Assert.Equal(BinaryOp.Mul, Assert.IsType<Expr.Binary>(raw.Root.Output[0]).Op);
            }
        }
    }
}
