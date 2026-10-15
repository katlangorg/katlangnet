using static KatLang.Tests.SixRouteAgreement;

namespace KatLang.Tests;

public class RestrictedLeadingContinuationTests
{
    [Theory]
    [InlineData("1", "+", "2", "3")]
    [InlineData("8", "/", "2", "4")]
    [InlineData("10", "div", "3", "3")]
    [InlineData("10", "mod", "3", "1")]
    [InlineData("2", "^", "3", "8")]
    [InlineData("1", "<", "2", "true")]
    [InlineData("2", ">", "1", "true")]
    [InlineData("1", "<=", "1", "true")]
    [InlineData("2", ">=", "2", "true")]
    [InlineData("2", "==", "2", "true")]
    [InlineData("1", "!=", "2", "true")]
    [InlineData("true", "and", "false", "false")]
    [InlineData("true", "or", "false", "true")]
    [InlineData("true", "xor", "false", "true")]
    public async Task EveryApprovedOperator_PreservesAstPrecedenceAndValue(
        string left, string op, string right, string expected)
    {
        var oneLine = $"{left} {op} {right}";
        foreach (var gap in new[] { "\n", "\r\n", " # trailing\n# intervening\n", "\n\n\t ", "\n    " })
        {
            var multiline = $"{left}{gap}{op} {right}";
            foreach (var template in new[] { "{0}", "P = {0}\nP", "F(x) = {0}\nF(0)",
                "a, b = {0}, 7\na, b", "{{{0}}}", "Id(x) = x\nId({0})", "[{0}]", "[10, 20][{0}]" })
                AssertSameAst(string.Format(template, oneLine), string.Format(template, multiline));
        }
        var observed = await OnEveryRouteAsync($"P = {left}\n{op} {right}\nP");
        Assert.Equal("ok", observed.Kind);
        Assert.Equal(expected, observed.Value);
        Assert.Empty(observed.Errors);
    }

    [Theory]
    [InlineData("1 + 2 * 3", "1\n+ 2 * 3")]
    [InlineData("-2 ^ 2 ^ 3", "-2\n^ 2\n^ 3")]
    [InlineData("1 < 2 <= 3 != 4", "1\n< 2\n<= 3\n!= 4")]
    [InlineData("true and false xor true or false", "true\nand false\nxor true\nor false")]
    [InlineData("not 1 < 2 and true", "not 1\n< 2\nand true")]
    public void MixedPrecedenceAndComparisonSpines_AreTheOneLineAst(string inline, string multiline)
        => AssertSameAst(inline, multiline);

    [Fact]
    public async Task ComparisonChain_DemandsEachOperandOnceInOrderAcrossSixRoutes()
    {
        const string source = "trace(1)\n< trace(2)\n<= trace(3)\n!= trace(4)";
        var chain = Assert.IsType<Expr.Comparison>(Assert.Single(SourceProvenance.ParseSyntaxValidRoot(source).Output));
        Assert.Equal(3, chain.Links.Count);
        Assert.All(chain.Links, link => Assert.IsNotType<Expr.Comparison>(link.Operand));
        var observed = await OnEveryRouteAsync(source);
        Assert.Equal("true", observed.Value);
        Assert.Equal("trace(1) | trace(2) | trace(3) | trace(4)", string.Join(" | ", observed.HostCalls));
        Assert.Empty(observed.Errors);
    }

    [Theory]
    [InlineData("P = {0}\nP", "S[1, 2, 3]")]
    [InlineData("F(x) = {0}\nF(0)", "S[1, 2, 3]")]
    [InlineData("F(0) = {0}\nF(n) = n,n,n\nF(0)", "S[1, 2, 3]")]
    [InlineData("a, b, c = {0}\na, b, c", "S[1, 2, 3]")]
    [InlineData("{0}", "S[1, 2, 3]")]
    [InlineData("{{{0}}}", "S[1, 2, 3]")]
    [InlineData("({0})", "S[1, 2, 3]")]
    [InlineData("[{0}]", "L[1, 2, 3]")]
    [InlineData("F(a,b,c) = a,b,c\nF({0})", "S[1, 2, 3]")]
    [InlineData("[10,20,30,40][{0}]", "S[20, 30, 40]")]
    public async Task LeadingCommas_KeepExactSlotStructure(string template, string expected)
    {
        var inline = string.Format(template, "1, 2, 3");
        var leading = string.Format(template, "1\n, 2\n, 3");
        AssertSameAst(inline, string.Format(template, "1,\n2,\n3"));
        AssertSameAst(inline, leading);
        var observed = await OnEveryRouteAsync(leading);
        Assert.Equal("ok", observed.Kind);
        Assert.Equal(expected, observed.Value);
        Assert.Empty(observed.Errors);
    }

    [Theory]
    [InlineData("10\n-2", "S[10, -2]")]
    [InlineData("A = 1\n-2\nA", "S[-2, 1]")]
    [InlineData("10 -\n2", "8")]
    [InlineData("true\nnot false", "S[true, true]")]
    [InlineData("F=10\nF\n(1)", "S[10, 1]")]
    [InlineData("F=10\nF\n{1}", "S[10, 1]")]
    [InlineData("Data=[10,20]\nData\n[0]", "S[L[10, 20], L[0]]")]
    [InlineData("F(x)=x+1\nF(\n1\n)", "2")]
    [InlineData("[10,20][\n0\n]", "10")]
    public async Task IndependentExpressionStarters_DoNotContinueThePreviousRow(string source, string expected)
    {
        var observed = await OnEveryRouteAsync(source);
        Assert.Equal("ok", observed.Kind);
        Assert.Equal(expected, observed.Value);
        Assert.Empty(observed.Errors);
    }

    [Fact]
    public async Task LeadingDots_PreserveFluentChains()
    {
        const string prelude = "Data=[1,2,3]\nP(x)=x>1\nF(x)=x*2\n";
        const string chain = "Data\n.filter(P)\n.map(F)\n.order\n.first";
        AssertSameAst(prelude + "Data.filter(P).map(F).order.first", prelude + chain);
        var observed = await OnEveryRouteAsync(prelude + chain);
        Assert.Equal("4", observed.Value);
        Assert.Empty(observed.Errors);
    }

    [Theory]
    [InlineData("+", "Good = 41")]
    [InlineData("/", "Good(x) = x")]
    [InlineData("<", "a, b = 40, 41")]
    [InlineData("^", "public Good = 41")]
    [InlineData(",", "~Good = 41")]
    [InlineData("and", "true = 41")]
    [InlineData("+", "open M")]
    public void Continuation_NeverConsumesADeclarationHead(string token, string head)
    {
        foreach (var source in new[] { $"P = 1 {token}\n{head}\nLater = 42\nLater",
            $"P = 1\n{token} {head}\nLater = 42\nLater" })
        {
            var parsed = Parser.ParseSyntax(source);
            Assert.True(parsed.HasErrors);
            Assert.Contains(parsed.Root.Properties, p => p.Name == "Later");
            var later = Assert.Single(parsed.Root.Properties, p => p.Name == "Later");
            Assert.Equal(42m, Assert.IsType<Expr.Num>(Assert.Single(later.Value.Output)).Value);
            Assert.Contains(parsed.Diagnostics, d => d.Code == DiagnosticCode.UnexpectedToken
                && d.Message.Contains("declaration", StringComparison.Ordinal));
            if (head.Contains("Good", StringComparison.Ordinal))
                Assert.Contains(parsed.Root.Properties, p => p.Name == "Good");
            if (head.StartsWith("a,", StringComparison.Ordinal))
            {
                Assert.Contains(parsed.Root.Properties, p => p.Name == "a");
                Assert.Contains(parsed.Root.Properties, p => p.Name == "b");
            }
        }
    }

    [Theory]
    [InlineData("X = a + b = c", "b")]
    [InlineData("X = a < b = c", "b")]
    [InlineData("X = a and b = c", "b")]
    [InlineData("F(a, b) = a - b = c", "b")]
    [InlineData("X = -b = c", "b")]
    [InlineData("Data = [1]\nIsEmpty = Data.count = 0", "count")]
    [InlineData("A = { b = 1 }\nX = A.b = 3", "b")]
    [InlineData("A = 1\nA\n.B.c = 2", "c")]
    [InlineData("[1, x = 2]", "x")]
    [InlineData("F(x) = x\nF(1, x = 2)", "x")]
    [InlineData("(1, x = 2)", "x")]
    public void MidLineContinuationTokens_NeverPromoteAHeadIntoADeclaration(string source, string head)
    {
        // Head protection is for a head on a LATER line or one sharing the line of a LEADING
        // continuation token. A name after a mid-line operator, comma or dot is no row start:
        // it stays the operand/member and its '=' keeps the same-line stray-'=' diagnostic,
        // never a fabricated declaration (which would also shadow, e.g., the prelude `count`).
        foreach (var newline in new[] { "\n", "\r\n" })
        {
            var parsed = Parser.ParseSyntax(source.Replace("\n", newline, StringComparison.Ordinal));
            Assert.True(parsed.HasErrors);
            Assert.DoesNotContain(parsed.Root.Properties, p => p.Name == head);
            var equals = Assert.Single(parsed.Diagnostics, d => d.Message.StartsWith("Unexpected '='.", StringComparison.Ordinal));
            Assert.Contains("To compare values, use '=='.", equals.Message, StringComparison.Ordinal);
            Assert.DoesNotContain(parsed.Diagnostics, d => d.Message.Contains("never continues an expression", StringComparison.Ordinal)
                || d.Message.Contains("cannot be a dot member", StringComparison.Ordinal));
        }

        // The leading-token spelling of the same head keeps Q-65's protection.
        var leading = Parser.ParseSyntax("1\n+ Good = 41\nLater = 42\nLater");
        Assert.Contains(leading.Root.Properties, p => p.Name == "Good");
    }

    [Theory]
    [InlineData("P={1\n+ }\nLater=42\nLater")]
    [InlineData("P=(1\n+ ]\nLater=42\nLater")]
    [InlineData("P=[1\n, }\nLater=42\nLater")]
    public void MalformedContinuation_PreservesClosersAndLaterDeclarations(string source)
    {
        var parsed = Parser.ParseSyntax(source);
        Assert.True(parsed.HasErrors);
        Assert.Contains(parsed.Root.Properties, p => p.Name == "Later");
    }

    [Fact]
    public void ReportedCharacters_RemainInvisibleToContinuation()
    {
        var parsed = Parser.ParseSyntax("P=1\n@\n+ 2\n@\n, 3\nP");
        Assert.Equal(2, parsed.Diagnostics.Count);
        Assert.All(parsed.Diagnostics, d => Assert.Equal(DiagnosticCode.UnexpectedCharacter, d.Code));
        Assert.Equal(LeanAstEncoder.EncodeProgram(SourceProvenance.ParseSyntaxValidRoot("P=1+2,3\nP")),
            LeanAstEncoder.EncodeProgram(parsed.Root));
    }

    [Fact]
    public void StarRemainsSeparate_AndPatternSeparatorsRemainTheirOwnGrammar()
    {
        foreach (var gap in new[] { "\n", " # c\n\n# c\n" })
        {
            // Issue #183: an attached line-final star completes its spread row, a detached
            // one is multiplication that continues; a leading star attaches backward.
            AssertSameAst("A*, B", $"A*{gap}B");
            AssertSameAst("A * B", $"A *{gap}B");
            AssertSameAst("A*, B", $"A*,{gap}B");
            AssertSameAst("A * B", $"A{gap}* B");
            var dangling = Parser.ParseSyntax($"A *{gap}B=2");
            Assert.True(dangling.HasErrors);
            Assert.Contains(dangling.Root.Properties, p => p.Name == "B");
            var completed = Parser.ParseSyntax($"A*{gap}B=2");
            Assert.False(completed.HasErrors);
            Assert.Contains(completed.Root.Properties, p => p.Name == "B");
            Assert.IsType<Expr.SequenceSpread>(Assert.Single(completed.Root.Output));
        }
        Assert.True(Parser.ParseSyntax("F(a\nb)=a\nF(1)").HasErrors);
        AssertSameAst("F(a,b)=a+b", "F(a\n,b)=a+b");
    }

    [Fact]
    public void LeadingGrace_IsItsOwnNameOccurrence()
    {
        var root = SourceProvenance.ParseSyntaxValidRoot("A\n~B");
        Assert.Equal(2, root.Output.Count);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(root.Output[0]).Name);
        Assert.IsType<Expr.Grace>(root.Output[1]);
    }

    private static void AssertSameAst(string inline, string multiline)
        => Assert.Equal(LeanAstEncoder.EncodeProgram(SourceProvenance.ParseSyntaxValidRoot(inline)),
            LeanAstEncoder.EncodeProgram(SourceProvenance.ParseSyntaxValidRoot(multiline)));
}
