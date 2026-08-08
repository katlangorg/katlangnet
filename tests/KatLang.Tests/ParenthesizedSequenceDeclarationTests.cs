namespace KatLang.Tests;

/// <summary>
/// Delimiter-model contract for parentheses: <c>( ... )</c> is sequence /
/// expression grouping (and call-argument syntax) ONLY. Algorithm-level
/// declarations — <c>open</c>, property definitions, callable (clause)
/// definitions, and deconstruction bindings — belong to <c>{ ... }</c> scoped
/// blocks or the root, never inside parentheses. The parser rejects them with
/// a targeted diagnostic; such programs must never evaluate successfully.
/// <c>[ ... ]</c> stays list construction with no declaration support.
/// </summary>
public class ParenthesizedSequenceDeclarationTests
{
    private const string OpenInParenthesesMessage =
        "An 'open' declaration is not allowed inside parentheses. Use a `{ ... }` block for a scoped algorithm.";

    private const string PropertyInParenthesesMessage =
        "A property declaration is not allowed inside parentheses. Use a `{ ... }` block for a scoped algorithm.";

    private const string Module = "M = { public P = 5 }\n";

    private static Diagnostic SingleDiagnostic(string source, string expectedMessage)
    {
        var result = Parser.ParseSyntax(source);
        Assert.True(result.HasErrors);
        return Assert.Single(result.Diagnostics, d => d.Message == expectedMessage);
    }

    private static void AssertSpan(
        string source,
        Diagnostic diagnostic,
        int startLine, int startColumn, int endLine, int endColumn,
        string expectedSlice)
    {
        Assert.Equal(DiagnosticSeverity.Error, diagnostic.Severity);
        Assert.Equal(startLine, diagnostic.Span.StartLineNumber);
        Assert.Equal(startColumn, diagnostic.Span.StartColumn);
        Assert.Equal(endLine, diagnostic.Span.EndLineNumber);
        Assert.Equal(endColumn, diagnostic.Span.EndColumn);
        Assert.Equal(expectedSlice, SourceSlice(source, diagnostic.Span));
    }

    private static string SourceSlice(string source, SourceSpan span)
    {
        Assert.Equal(span.StartLineNumber, span.EndLineNumber);
        var line = source.Split('\n')[span.StartLineNumber - 1].TrimEnd('\r');
        return line.Substring(span.StartColumn - 1, span.EndColumn - span.StartColumn + 1);
    }

    private static void AssertRejected(string source, string expectedMessage)
    {
        // Parser-level rejection, not a downstream evaluation accident.
        var parsed = Parser.ParseSyntax(source);
        Assert.True(parsed.HasErrors);
        Assert.Contains(parsed.Diagnostics, d => d.Message == expectedMessage);

        // The engine surfaces it as a parse failure; no successful evaluation.
        var run = KatLangEngine.Run(source);
        var failure = Assert.IsType<RunResult.ParseFailure>(run);
        Assert.Contains(failure.Errors, e => e.Message == expectedMessage);
    }

    // ── `open` is rejected inside parentheses, whatever the output kind ─────

    [Theory]
    [InlineData("P")]        // Resolve
    [InlineData("P + 1")]    // Binary
    [InlineData("F(P)")]     // Call
    [InlineData("P.max")]    // DotCall
    [InlineData("[P]")]      // ListLiteral
    [InlineData("1, P")]     // multiple outputs
    [InlineData("5")]        // Num
    [InlineData("(P)")]      // nested group
    public void OpenInParenthesizedGroup_IsRejected_ForEveryOutputKind(string body)
        => AssertRejected($"{Module}F(x) = x\n(open M\n{body})", OpenInParenthesesMessage);

    [Fact]
    public void OpenInGroup_DiagnosticSpansTheOpenDeclaration()
    {
        const string source = "M = { public P = 5 }\n(open M\nP)";
        var diagnostic = SingleDiagnostic(source, OpenInParenthesesMessage);
        AssertSpan(source, diagnostic, 2, 2, 2, 7, "open M");
    }

    [Fact]
    public void OpenInGroup_MultipleTargets_DiagnosticSpansTheWholeTargetList()
    {
        const string source = "M = { public P = 5 }\nN = { public Q = 1 }\n(open M, N\nP + Q)";
        var diagnostic = SingleDiagnostic(source, OpenInParenthesesMessage);
        AssertSpan(source, diagnostic, 3, 2, 3, 10, "open M, N");
    }

    [Fact]
    public void OpenInPropertyValueGroup_IsRejected()
        // The former module-body-in-parentheses idiom: a lone parenthesized
        // group as a property body no longer smuggles in declarations.
        => AssertRejected(
            "M = { public P = 5 }\nY = (\n    open M\n    P + 1\n)\nY",
            OpenInParenthesesMessage);

    [Fact]
    public void OpenInNestedGroupInsideCallArguments_IsRejected()
        => AssertRejected(
            "M = { public P = 5 }\nIdentity(x) = x\nIdentity((\n    open M\n    P + 1\n))",
            OpenInParenthesesMessage);

    [Fact]
    public void OpenDirectlyInsideCallArguments_IsRejected()
        // Call-argument lists are parentheses too: declarations belong to a
        // brace block argument, `Identity({ open M ... })`.
        => AssertRejected(
            "M = { public P = 5 }\nIdentity(x) = x\nIdentity(open M\nP + 1)",
            OpenInParenthesesMessage);

    [Fact]
    public void OpenInParenthesizedOpenTargetBundle_IsRejected()
        // An inline bundle as an open target must be a brace block
        // (`open { ... }`), never a parenthesized group with declarations.
        => AssertRejected("(open M\n1)\nM = { public P = 5 }", OpenInParenthesesMessage);

    // ── property declarations are rejected inside parentheses ───────────────

    [Fact]
    public void LocalPropertyInGroup_IsRejected()
        => AssertRejected("(\n    A = 5\n    A + 1\n)", PropertyInParenthesesMessage);

    [Fact]
    public void LocalPropertyInGroup_DiagnosticSpansThePropertyName()
    {
        const string source = "(\nA = 5\nA + 1\n)";
        var diagnostic = SingleDiagnostic(source, PropertyInParenthesesMessage);
        AssertSpan(source, diagnostic, 2, 1, 2, 1, "A");
    }

    [Fact]
    public void PublicPropertyInGroup_IsRejected()
        // The former `Library = (public Value = 7)` module idiom: modules are
        // brace blocks now.
        => AssertRejected("Library = (\n    public Value = 7\n)\nLibrary.Value", PropertyInParenthesesMessage);

    [Fact]
    public void LocalCallablePropertyInGroup_IsRejected()
        => AssertRejected("(\n    A(x) = x + 1\n    A(5)\n)", PropertyInParenthesesMessage);

    [Fact]
    public void PublicCallablePropertyInGroup_IsRejected()
        => AssertRejected(
            "(\n    public A(x) = x + 1\n    A(5)\n)",
            PropertyInParenthesesMessage);

    [Fact]
    public void MultiClauseDefinitionInGroup_IsRejected()
        => AssertRejected(
            "(\n    A(0) = 1\n    A(x) = x + 1\n    A(5)\n)",
            PropertyInParenthesesMessage);

    [Fact]
    public void LocalCallablePropertyInGroup_DiagnosticSpansTheClauseName()
    {
        const string source = "(\nA(x) = x + 1\nA(5)\n)";
        var diagnostic = SingleDiagnostic(source, PropertyInParenthesesMessage);
        AssertSpan(source, diagnostic, 2, 1, 2, 1, "A");
    }

    [Fact]
    public void DeconstructionBindingInGroup_IsRejected()
        => AssertRejected("(\nx, y = 7, 8\nx + y\n)", PropertyInParenthesesMessage);

    [Fact]
    public void LoneCollectingBindingInGroup_IsRejected()
        => AssertRejected("(\n*items = 1, 2, 3\nitems\n)", PropertyInParenthesesMessage);

    [Fact]
    public void DeconstructionBindingInGroup_DiagnosticSpansTheBindingPattern()
    {
        const string source = "(\nx, *y = 7, 8\nx\n)";
        var diagnostic = SingleDiagnostic(source, PropertyInParenthesesMessage);
        AssertSpan(source, diagnostic, 2, 1, 2, 5, "x, *y");
    }

    [Fact]
    public void LocalPropertyInNestedGroupInsideCallArguments_IsRejected()
        => AssertRejected(
            "Identity(x) = x\nIdentity((\n    A = 5\n    A\n))",
            PropertyInParenthesesMessage);

    [Fact]
    public void PropertyDirectlyInsideCallArguments_IsRejected()
        => AssertRejected(
            "Identity(x) = x\nIdentity(A = 5\nA + 1)",
            PropertyInParenthesesMessage);

    // ── recovery keeps the group's structure without inventing semantics ────

    [Fact]
    public void RejectedGroup_RecoveryKeepsOpensOnTheBlock()
    {
        // The rejection diagnostic is authoritative; recovery still retains
        // the parsed declarations instead of silently discarding them, so
        // downstream tooling sees a truthful (if invalid) tree.
        var result = Parser.ParseSyntax("M = { public P = 5 }\n(open M\nP + 1)");
        Assert.True(result.HasErrors);
        var block = Assert.IsType<Expr.Block>(Assert.Single(result.Root.Output));
        var open = Assert.Single(block.Algorithm.Opens);
        Assert.Equal("M", Assert.IsType<Expr.Resolve>(open).Name);
    }

    [Fact]
    public void RejectedGroup_RecoveryKeepsPropertiesOnTheBlock()
    {
        var result = Parser.ParseSyntax("(\nA = 5\nA + 1\n)");
        Assert.True(result.HasErrors);

        var block = Assert.IsType<Expr.Block>(Assert.Single(result.Root.Output));
        var property = Assert.Single(block.Algorithm.Properties);
        Assert.Equal("A", property.Name);
        Assert.IsType<Expr.Num>(Assert.Single(property.Value.Output));
        Assert.IsType<Expr.Binary>(Assert.Single(block.Algorithm.Output));
    }

    // ── valid parentheses keep their grouping/sequence role ─────────────────

    [Theory]
    [InlineData("(1)", "1")]
    [InlineData("(1 + 2)", "3")]
    [InlineData("(1, 2)", "(1, 2)")]
    [InlineData("((1, 2), 3)", "((1, 2), 3)")]
    [InlineData("([1, 2])", "[1, 2]")]
    [InlineData("()", "()")]
    [InlineData("(())", "()")]
    [InlineData("((()))", "()")]
    [InlineData("((1, 2)).count", "2")]
    [InlineData("F(x) = x\n(F(1))", "1")]
    [InlineData("[1, 2, 3]", "[1, 2, 3]")]
    public void ParenthesesWithoutDeclarations_ParseAndEvaluateUnchanged(string source, string expected)
    {
        var parsed = Parser.ParseSyntax(source);
        Assert.False(parsed.HasErrors);
        Assert.DoesNotContain(parsed.Diagnostics, d => d.Message.Contains("not allowed inside parentheses"));

        var result = KatLangEngine.Run(source);
        Assert.Equal(expected, Assert.IsType<RunResult.Success>(result).ToDisplayString());
    }
}
