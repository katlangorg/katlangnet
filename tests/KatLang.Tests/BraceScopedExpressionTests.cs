namespace KatLang.Tests;

/// <summary>
/// Delimiter-model contract for braces: <c>{ ... }</c> is the scoped
/// algorithm/block form and works wherever an expression-valued block is
/// allowed — property values, function arguments, nested blocks. A brace
/// block owns its declarations: its <c>open</c> targets and local properties
/// resolve inside the block and never become phantom implicit parameters of
/// the surrounding algorithm, and nothing declared or opened inside leaks out.
/// </summary>
public class BraceScopedExpressionTests
{
    private const string Module = "M = {\n    public P = 5\n}\n";

    private static string RunDisplay(string source)
    {
        var result = KatLangEngine.Run(source);
        return Assert.IsType<RunResult.Success>(result).ToDisplayString();
    }

    // ── A: open in property value ────────────────────────────────────────────

    [Fact]
    public void OpenInBracePropertyValue_Evaluates()
        => Assert.Equal("6", RunDisplay(Module + "Y = {\n    open M\n    P + 1\n}\nY"));

    [Fact]
    public void OpenInBracePropertyValue_BlockOwnsTheOpen_AndNoImplicitParameterLeaks()
    {
        var result = Parser.Parse(Module + "Y = {\n    open M\n    P + 1\n}\nY");
        Assert.False(result.HasErrors);

        var y = Assert.Single(result.Root.Properties, p => p.Name == "Y");
        // The brace block is adopted as Y's own body: it owns the open target.
        var open = Assert.Single(y.Value.Opens);
        Assert.Equal("M", Assert.IsType<Expr.Resolve>(open).Name);
        // `P` resolves through the block's own open — no implicit parameter.
        Assert.Empty(y.Value.Params);
        Assert.Empty(result.Root.Params);
    }

    // ── B: open in function-argument position ───────────────────────────────

    private const string OpenArgumentSource =
        "M = {\n    public P = 5\n}\n\nIdentity(x) = x\n\nIdentity({\n    open M\n    P + 1\n})";

    [Fact]
    public void OpenInBraceArgument_Evaluates()
        => Assert.Equal("6", RunDisplay(OpenArgumentSource));

    [Fact]
    public void OpenInBraceArgument_RawAstRetainsTheBraceBlockWithItsOpen()
    {
        var result = Parser.ParseSyntax(OpenArgumentSource);
        Assert.False(result.HasErrors);

        var call = Assert.IsType<Expr.Call>(Assert.Single(result.Root.Output));
        var block = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(call.Args));
        var open = Assert.Single(block.Algorithm.Opens);
        Assert.Equal("M", Assert.IsType<Expr.Resolve>(open).Name);
    }

    [Fact]
    public void OpenInBraceArgument_NoPhantomOuterParameter()
    {
        var result = Parser.Parse(OpenArgumentSource);
        Assert.False(result.HasErrors);
        // `P` is provided by the block's own open: neither the root nor the
        // elaborated argument block may hoist it as an implicit parameter.
        Assert.Empty(result.Root.Params);

        var call = Assert.IsType<Expr.Call>(Assert.Single(result.Root.Output));
        var block = Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(call.Args));
        Assert.Single(block.Algorithm.Opens);
        Assert.Empty(block.Algorithm.Params);
    }

    // ── C: local property in function-argument position ─────────────────────

    [Fact]
    public void LocalPropertyInBraceArgument_Evaluates()
        => Assert.Equal("6", RunDisplay("Identity(x) = x\n\nIdentity({\n    A = 5\n    A + 1\n})"));

    [Fact]
    public void LocalPropertyInBraceArgument_NoPhantomOuterParameter()
    {
        var result = Parser.Parse("Identity(x) = x\n\nIdentity({\n    A = 5\n    A + 1\n})");
        Assert.False(result.HasErrors);
        Assert.Empty(result.Root.Params);
    }

    // ── D: nested brace scopes compose lexically ────────────────────────────

    [Fact]
    public void NestedBraceScopes_InnerBlockSeesOuterOpen()
        // The outer block opens M; the inner block's property uses the opened
        // name through the lexical parent chain and produces the output.
        => Assert.Equal("6", RunDisplay(
            Module + "\nIdentity(x) = x\n\nIdentity({\n    open M\n\n    {\n        A = P + 1\n        A\n    }\n})"));

    [Fact]
    public void NestedBraceScopes_InnerLocalPropertyDoesNotLeakUpward()
    {
        // `A` is declared in the inner block only; the outer block and root
        // must not see it as a property or hoist it as a parameter.
        var result = Parser.Parse("Identity(x) = x\nIdentity({\n    {\n        A = 5\n        A + 1\n    }\n})");
        Assert.False(result.HasErrors);
        Assert.Empty(result.Root.Params);
        Assert.Equal("6", RunDisplay("Identity(x) = x\nIdentity({\n    {\n        A = 5\n        A + 1\n    }\n})"));
    }

    // ── E: block scope does not leak outward ────────────────────────────────

    [Fact]
    public void OpenInsideBraceBlock_DoesNotExposeTheNameAfterTheBlock()
    {
        // After Y's block, `P` is not in scope: it falls back to the standard
        // implicit-parameter convention on the root and evaluation fails
        // because no argument supplies it.
        var source = Module + "Y = {\n    open M\n    P\n}\nY + P";
        var parsed = Parser.Parse(source);
        Assert.False(parsed.HasErrors);
        Assert.Equal("P", Assert.Single(parsed.Root.Params));

        Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
    }

    [Fact]
    public void LocalPropertyInsideBraceArgument_DoesNotLeakToFollowingOutput()
    {
        var source = "Identity(x) = x\nIdentity({\n    A = 5\n    A\n})\nA";
        var parsed = Parser.Parse(source);
        Assert.False(parsed.HasErrors);
        Assert.Equal("A", Assert.Single(parsed.Root.Params));

        Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source));
    }

    // ── plain brace controls ─────────────────────────────────────────────────

    [Theory]
    [InlineData("{ 1 }", "1")]
    [InlineData("F(x) = x\nF({ 1 })", "1")]
    [InlineData("{\n    A = 5\n    A + 1\n}", "6")]
    public void PlainBraceBlocks_EvaluateUnchanged(string source, string expected)
        => Assert.Equal(expected, RunDisplay(source));
}
