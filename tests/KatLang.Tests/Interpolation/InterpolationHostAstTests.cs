namespace KatLang.Tests.Interpolation;

/// <summary>
/// STR-02 over host-built ASTs (<see cref="Evaluator"/> evaluates a host-built
/// <see cref="Expr"/> as-is): every shape the record admits evaluates by the same rule — the
/// head, then each link's hole value text and text — including shapes the parser never produces
/// (no links, empty texts, a hole-free node), a shared hole is evaluated once per OCCURRENCE,
/// and the structural preflight bounds an arbitrarily deep host nesting with its structured
/// depth error instead of the host stack.
/// </summary>
public class InterpolationHostAstTests
{
    private static string Text(Expr expr)
    {
        var result = Evaluator.Run(expr);
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        return Assert.IsType<Result.Str>(result.Value).Value;
    }

    private static Expr.InterpolatedString Interpolate(string head, params (Expr Hole, string Text)[] links)
        => new(head, links.Select(l => new InterpolationLink(l.Hole, l.Text)).ToArray());

    [Fact]
    public void ANodeWithoutLinks_IsItsHeadText()
    {
        Assert.Equal("only", Text(Interpolate("only")));
        Assert.Equal("", Text(Interpolate("")));
    }

    [Fact]
    public void EmptyTexts_AndAdjacentHoles_Concatenate()
        => Assert.Equal("12", Text(Interpolate("", (new Expr.Num(1), ""), (new Expr.Num(2), ""))));

    [Fact]
    public void HostText_IsUsedVerbatim_NeverDecodedOrReparsed()
        => Assert.Equal("{\\n}\"", Text(Interpolate("{\\n", (new Expr.StringLiteral("}"), "\""))));

    [Fact]
    public void AHostNodeWithoutHoles_EqualsTheStringLiteral()
    {
        var root = new Expr.Comparison(Interpolate("abc"), [new ComparisonLink(ComparisonOp.Eq, new Expr.StringLiteral("abc"))]);
        Assert.Equal(new Result.Bool(true), Evaluator.Run(root).Value);
    }

    [Fact]
    public void ASharedHoleNode_IsEvaluatedOncePerOccurrence()
    {
        var log = new List<decimal>();
        var operations = HostOperations.Create(HostOperation.Create("Log", (args, _) =>
        {
            log.Add((decimal)Assert.IsType<Result.Atom>(args[0]).Value);
            return args[0];
        }, "x"));
        // One hole node referenced by two links: the host operation resolves through the prelude.
        Expr shared = new Expr.Call(new Expr.Resolve("Log"), new OutputBundle([new Expr.Num(1)]));
        var doubled = Interpolate("", (shared, "-"), (shared, ""));

        var result = Evaluator.Run(doubled, operations, limits: null, randomSeed: null, CancellationToken.None);
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        Assert.Equal("1-1", Assert.IsType<Result.Str>(result.Value).Value);
        Assert.Equal(new decimal[] { 1, 1 }, log);
    }

    [Fact]
    public void DeepHostNesting_IsTheStructuredDepthError()
    {
        Expr expr = new Expr.Num(1);
        for (var i = 0; i < 10_000; i++)
            expr = Interpolate("", (expr, ""));
        var result = Evaluator.Run(expr);
        Assert.IsType<EvalError.AstDepthLimitExceeded>(result.Error);
    }

    [Fact]
    public void NestingAtTheCeiling_EvaluatesIteratively()
    {
        // Two depth units per interpolation node: 149 levels around a leaf reach depth 299.
        Expr expr = new Expr.Num(7);
        for (var i = 0; i < (EvaluationLimits.MaxSupportedAstDepth - 1) / 2; i++)
            expr = Interpolate("<", (expr, ">"));
        var text = Text(expr);
        Assert.Equal(149 * 2 + 1, text.Length);
        Assert.Equal('7', text[149]);
    }

    [Fact]
    public void AHoleFailure_WithoutASpan_TakesTheNodesSpan()
    {
        var span = new SourceSpan(3, 1, 3, 9);
        var node = Interpolate("x", (new Expr.Binary(BinaryOp.Div, new Expr.Num(1), new Expr.Num(0)), "")) with { Span = span };
        var error = Evaluator.Run(node).Error;
        Assert.IsType<EvalError.DivByZero>(error);
        Assert.Equal(span, error.Span);
    }

    [Fact]
    public void AnInterpolatedString_IsNoAlgorithm()
    {
        var call = new Expr.Call(Interpolate("f"), new OutputBundle([new Expr.Num(1)]));
        var error = Evaluator.Run(call).Error;
        while (error is EvalError.WithContext context)
            error = context.Inner;
        Assert.Equal("interpolated string", Assert.IsType<EvalError.NotAnAlgorithm>(error).Description);
    }
}
