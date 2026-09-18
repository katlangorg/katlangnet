using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// F5: a unary operator applied to an operand that fails numeric conversion — the
/// empty sequence value, a multi-item sequence value, or a list value — reports
/// <see cref="EvalError.BadArity"/> AT the written unary expression, on every
/// evaluation path (plain, counted, the async twin, and the engine's error
/// projection) and for every operand shape: the same location policy the unary
/// string rejection and the binary operators' operand rejections already followed.
/// Before this pin the error was structurally spanless, so a host could not point
/// at the failing expression at all. The error KIND is unchanged (BadArity, the
/// host-facing <see cref="KatLangErrorCode.ArityMismatch"/> family) — the fix
/// locates the failure, it never re-classifies it.
/// </summary>
public class UnaryBadAritySpanTests
{
    private static EvalError Innermost(EvalError error)
        => error is EvalError.WithContext withContext ? Innermost(withContext.Inner) : error;

    private static Expr Program(string source)
        => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

    public static TheoryData<string, string, SourceSpan> FailingUnaryOperands() => new()
    {
        { "minus multi-item sequence", "-(1, 2)", new SourceSpan(1, 1, 1, 8) },
        { "not multi-item sequence", "not (1, 2)", new SourceSpan(1, 1, 1, 11) },
        { "minus empty sequence", "-()", new SourceSpan(1, 1, 1, 4) },
        { "not empty sequence", "not ()", new SourceSpan(1, 1, 1, 7) },
        { "minus list", "-[1, 2]", new SourceSpan(1, 1, 1, 8) },
        { "not list", "not [1, 2]", new SourceSpan(1, 1, 1, 11) },
        { "grouped invalid operand", "-((1, 2))", new SourceSpan(1, 1, 1, 10) },
        { "not grouped invalid operand", "not ((1, 2))", new SourceSpan(1, 1, 1, 13) },
        { "nested unary with inner failure", "-(-(1, 2))", new SourceSpan(1, 2, 1, 11) },
        { "nested not with inner failure", "not (-(1, 2))", new SourceSpan(1, 5, 1, 14) },
        { "multiple groups of the failing unary", "not ((-()))", new SourceSpan(1, 5, 1, 12) },
        { "property operand", "X = (1, 2)\n-X", new SourceSpan(2, 1, 2, 3) },
        { "operand inside a binary expression", "1 + -(1, 2)", new SourceSpan(1, 5, 1, 12) },
        { "operand inside a call argument", "F(v) = v\nF(-(1, 2))", new SourceSpan(2, 3, 2, 10) },
    };

    [Theory]
    [MemberData(nameof(FailingUnaryOperands))]
    public async Task EveryEvaluationPath_ReportsBadArityAtTheUnaryExpression(string label, string source, SourceSpan expected)
    {
        Assert.False(string.IsNullOrEmpty(label));
        var ast = Program(source);

        var plain = Evaluator.Run(ast);
        Assert.True(plain.IsError);
        Assert.Equal(expected, Assert.IsType<EvalError.BadArity>(Innermost(plain.Error)).Span);

        var counted = Evaluator.RunCounted(ast);
        Assert.True(counted.IsError);
        Assert.Equal(expected, Assert.IsType<EvalError.BadArity>(Innermost(counted.Error)).Span);

        // The async twin completes synchronously through the pass-through seam and
        // must report the identical structured error.
        var twin = Evaluator.RunCountedAsync(ast, new PassThroughAsyncZeroArgPropertyResultCache());
        Assert.True(twin.IsCompleted);
        var twinResult = await twin;
        Assert.True(twinResult.IsError);
        Assert.Equal(expected, Assert.IsType<EvalError.BadArity>(Innermost(twinResult.Error)).Span);
        Assert.Equal(
            LoopDiagnosticParityAssertions.DescribeErrorTree(counted.Error),
            LoopDiagnosticParityAssertions.DescribeErrorTree(twinResult.Error));
    }

    [Fact]
    public void Engine_ProjectsTheUnaryExpressionSpanAndKeepsTheArityFamily()
    {
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run("-(1, 2)"));
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.ArityMismatch, error.Code);
        Assert.False(error.IsResourceLimit);
        Assert.Equal(new SourceSpan(1, 1, 1, 8), error.Span);

        var notFailure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run("X = ()\nnot X"));
        var notError = Assert.Single(notFailure.Errors);
        Assert.Equal(KatLangErrorCode.ArityMismatch, notError.Code);
        Assert.Equal(new SourceSpan(2, 1, 2, 6), notError.Span);
    }

    [Fact]
    public void NestedUnary_KeepsTheInnerUnarySpanAsTheInnermostError()
    {
        // `-(-(1, 2))`: the INNER unary fails. It is the grouped operand of the outer
        // `-`, so — per the grouped-expression span rule (F6) — its span is the
        // group's full extent `(-(1, 2))` (columns 2-10), and the outer unary never
        // overwrites an operand failure that already carries a span.
        var minus = Evaluator.Run(Program("-(-(1, 2))"));
        Assert.True(minus.IsError);
        Assert.Equal(new SourceSpan(1, 2, 1, 11), Assert.IsType<EvalError.BadArity>(Innermost(minus.Error)).Span);

        var not = Evaluator.Run(Program("not (-(1, 2))"));
        Assert.True(not.IsError);
        Assert.Equal(new SourceSpan(1, 5, 1, 14), Assert.IsType<EvalError.BadArity>(Innermost(not.Error)).Span);
    }

    [Theory]
    [InlineData("-(3)", "-3")]
    [InlineData("not (0)", "1")]
    [InlineData("-((3))", "-3")]
    [InlineData("-(1) + 4", "3")]
    [InlineData("X = (3)\n-X", "-3")]
    public void ValidUnaryOperands_EvaluateUnchanged(string source, string expected)
    {
        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));
        Assert.Equal(expected, success.ToDisplayString());
    }
}
