namespace KatLang.Tests;

/// <summary>
/// Exact source-span contracts for evaluator diagnostics. Each case uses a
/// prebuilt AST so front-end recovery cannot satisfy the assertion first.
/// </summary>
public class EvaluatorDiagnosticSpanTests
{
    private static readonly SourceSpan OuterSpan = new(10, 2, 10, 20);
    private static readonly SourceSpan InnerSpan = new(11, 4, 11, 14);

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void UnknownName_UsesTheResolveOccurrenceSpan(bool counted)
    {
        var expr = new Expr.Resolve("missing") { Span = InnerSpan };

        var error = RunError(expr, counted);

        Assert.IsType<EvalError.UnknownName>(Innermost(error));
        Assert.Equal(InnerSpan, Innermost(error).Span);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void IllegalExpression_UsesTheRejectedExpressionSpan(bool counted)
    {
        var expr = new Expr.Grace(new Expr.Num(1), Weight: 1) { Span = InnerSpan };

        var error = RunError(expr, counted);

        Assert.IsType<EvalError.IllegalInEval>(Innermost(error));
        Assert.Equal(InnerSpan, Innermost(error).Span);
    }

    [Theory]
    [InlineData(false, true)]
    [InlineData(false, false)]
    [InlineData(true, true)]
    [InlineData(true, false)]
    public void ZeroParameterBlock_ErrorUsesOuterSpanThenFallsBackToFirstOutputSpan(
        bool counted,
        bool hasOuterSpan)
    {
        var failingOutput = new Expr.Unary(
            UnaryOp.Minus,
            new Expr.Resolve("missing"))
        {
            Span = InnerSpan,
        };
        var block = User(output: OutputBundle.From([failingOutput]));
        var expr = new Expr.AlgorithmExpr(block)
        {
            Span = hasOuterSpan ? OuterSpan : null,
        };

        var error = RunError(expr, counted);

        Assert.IsType<EvalError.UnknownName>(Innermost(error));
        Assert.Contains(hasOuterSpan ? OuterSpan : InnerSpan, ErrorSpans(error));
    }

    [Theory]
    [InlineData(false, true)]
    [InlineData(false, false)]
    [InlineData(true, true)]
    [InlineData(true, false)]
    public void ParameterizedBlock_MissingArgumentsUseOuterThenFirstOutputSpan(
        bool counted,
        bool hasOuterSpan)
    {
        var block = User(
            parameters: [new ParameterDeclaration("x")],
            output: OutputBundle.From([new Expr.Num(1) { Span = InnerSpan }]));
        var expr = new Expr.AlgorithmExpr(block)
        {
            Span = hasOuterSpan ? OuterSpan : null,
        };

        var error = RunError(expr, counted);

        Assert.IsType<EvalError.UnresolvedImplicitParams>(Innermost(error));
        Assert.Equal(hasOuterSpan ? OuterSpan : InnerSpan, Innermost(error).Span);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void FailedCallContext_CopiesTheCalleeResolutionSpan(bool counted)
    {
        var callee = new Expr.Resolve("missing") { Span = InnerSpan };
        var call = new Expr.Call(callee, OutputBundle.Empty) { Span = OuterSpan };

        var error = RunError(call, counted);

        var context = Assert.IsType<EvalError.WithContext>(error);
        Assert.IsType<EvalError.UnknownName>(context.Inner);
        Assert.Equal(InnerSpan, context.Inner.Span);
        Assert.Equal(InnerSpan, context.Span);
    }

    [Fact]
    public void WithSpan_AttachesOnlyWhenTheErrorHasNoMoreSpecificSpan()
    {
        var unpositioned = Evaluator.WithSpan<Result>(OuterSpan, new EvalError.DivByZero());
        Assert.True(unpositioned.IsError);
        Assert.Equal(OuterSpan, unpositioned.Error.Span);

        var positionedError = new EvalError.DivByZero { Span = InnerSpan };
        var positioned = Evaluator.WithSpan<Result>(OuterSpan, positionedError);
        Assert.True(positioned.IsError);
        Assert.Same(positionedError, positioned.Error);
        Assert.Equal(InnerSpan, positioned.Error.Span);

        var noFallback = Evaluator.WithSpan<Result>(null, new EvalError.DivByZero());
        Assert.True(noFallback.IsError);
        Assert.Null(noFallback.Error.Span);
    }

    [Theory]
    [InlineData(UnaryOp.Minus, false)]
    [InlineData(UnaryOp.Minus, true)]
    [InlineData(UnaryOp.Not, false)]
    [InlineData(UnaryOp.Not, true)]
    public void UnaryStringFailure_UsesTheExactUnaryExpressionSpan(UnaryOp op, bool counted)
    {
        var expr = new Expr.Unary(op, new Expr.StringLiteral("text")) { Span = InnerSpan };

        var error = Assert.IsType<EvalError.TypeMismatch>(RunError(expr, counted));
        Assert.Equal(InnerSpan, error.Span);

        var rendered = KatLangError.FromEvalError(error);
        Assert.Equal(((int?)11, (int?)4, (int?)11, (int?)14),
            (rendered.StartLine, rendered.StartColumn, rendered.EndLine, rendered.EndColumn));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void NestedUnary_DoesNotOverwriteAnAlreadyPresentInnerStringSpan(bool counted)
    {
        var inner = new Expr.Unary(UnaryOp.Minus, new Expr.StringLiteral("text")) { Span = InnerSpan };
        var outer = new Expr.Unary(UnaryOp.Not, inner) { Span = OuterSpan };

        var error = Assert.IsType<EvalError.TypeMismatch>(RunError(outer, counted));
        Assert.Equal(InnerSpan, error.Span);

        var rendered = KatLangError.FromEvalError(error);
        Assert.Equal(((int?)11, (int?)4, (int?)11, (int?)14),
            (rendered.StartLine, rendered.StartColumn, rendered.EndLine, rendered.EndColumn));
    }

    [Fact]
    public void PreferExpressionSpan_UsesTheExpressionBeforeItsFirstOutputFallback()
    {
        var output = OutputBundle.From([new Expr.Num(1) { Span = InnerSpan }]);

        Assert.Equal(OuterSpan, Evaluator.PreferExpressionSpan(OuterSpan, output));
        Assert.Equal(InnerSpan, Evaluator.PreferExpressionSpan(null, output));
        Assert.Null(Evaluator.PreferExpressionSpan(null, OutputBundle.Empty));
    }

    private static Algorithm.User User(
        IReadOnlyList<ParameterDeclaration>? parameters = null,
        OutputBundle? output = null)
        => new(
            Parent: null,
            Parameters: parameters ?? [],
            Opens: [],
            Properties: [],
            Output: output ?? OutputBundle.Empty);

    private static EvalError RunError(Expr expr, bool counted)
    {
        if (counted)
        {
            var result = Evaluator.EvalCountedExpressionForTesting(expr);
            Assert.True(result.IsError);
            return result.Error;
        }

        var plain = Evaluator.EvalExpressionForTesting(expr);
        Assert.True(plain.IsError);
        return plain.Error;
    }

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;
        return error;
    }

    private static IReadOnlyList<SourceSpan> ErrorSpans(EvalError error)
    {
        var spans = new List<SourceSpan>();
        while (true)
        {
            if (error.Span is { } span)
                spans.Add(span);
            if (error is not EvalError.WithContext context)
                return spans;
            error = context.Inner;
        }
    }
}
