using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// F5: a unary operator applied to an operand it rejects reports the rejection AT the
/// written unary expression, on every evaluation path (plain, counted, the async twin,
/// and the engine's error projection) and for every operand shape — the same location
/// policy the unary string rejection and the binary operators' operand rejections
/// already followed. For unary minus the rejection is the numeric-conversion
/// <see cref="EvalError.BadArity"/> (the empty sequence value, a multi-item sequence
/// value, a list value); for unary <c>not</c> it is the Boolean-operand
/// <see cref="EvalError.TypeMismatch"/> (every non-Boolean operand). Before this pin
/// the error was structurally spanless, so a host could not point at the failing
/// expression at all. The fix locates each failure; it never re-classifies it.
/// </summary>
public class UnaryBadAritySpanTests
{
    private static EvalError Innermost(EvalError error)
        => error is EvalError.WithContext withContext ? Innermost(withContext.Inner) : error;

    private static Expr Program(string source)
        => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

    public static TheoryData<string, string, SourceSpan> FailingMinusOperands() => new()
    {
        { "minus multi-item sequence", "-(1, 2)", new SourceSpan(1, 1, 1, 8) },
        { "minus empty sequence", "-()", new SourceSpan(1, 1, 1, 4) },
        { "minus list", "-[1, 2]", new SourceSpan(1, 1, 1, 8) },
        { "grouped invalid operand", "-((1, 2))", new SourceSpan(1, 1, 1, 10) },
        { "nested unary with inner failure", "-(-(1, 2))", new SourceSpan(1, 2, 1, 11) },
        { "nested not with inner minus failure", "not (-(1, 2))", new SourceSpan(1, 5, 1, 14) },
        { "multiple groups of the failing unary", "not ((-()))", new SourceSpan(1, 5, 1, 12) },
        { "property operand", "X = (1, 2)\n-X", new SourceSpan(2, 1, 2, 3) },
        { "operand inside a binary expression", "1 + -(1, 2)", new SourceSpan(1, 5, 1, 12) },
        { "operand inside a call argument", "F(v) = v\nF(-(1, 2))", new SourceSpan(2, 3, 2, 10) },
    };

    public static TheoryData<string, string, SourceSpan> FailingNotOperands() => new()
    {
        { "not multi-item sequence", "not (1, 2)", new SourceSpan(1, 1, 1, 11) },
        { "not empty sequence", "not ()", new SourceSpan(1, 1, 1, 7) },
        { "not list", "not [1, 2]", new SourceSpan(1, 1, 1, 11) },
        { "not grouped invalid operand", "not ((1, 2))", new SourceSpan(1, 1, 1, 13) },
        { "not number", "not 0", new SourceSpan(1, 1, 1, 6) },
        { "not string", "not 'ab'", new SourceSpan(1, 1, 1, 9) },
        { "not property operand", "X = ()\nnot X", new SourceSpan(2, 1, 2, 6) },
        { "not inside a call argument", "F(v) = v\nF(not 1)", new SourceSpan(2, 3, 2, 8) },
    };

    [Theory]
    [MemberData(nameof(FailingMinusOperands))]
    public Task EveryEvaluationPath_ReportsBadArityAtTheUnaryExpression(string label, string source, SourceSpan expected)
        => AssertEveryPathReportsAtTheUnaryExpression<EvalError.BadArity>(label, source, expected);

    [Theory]
    [MemberData(nameof(FailingNotOperands))]
    public Task EveryEvaluationPath_ReportsTheBooleanOperandMismatchAtTheUnaryExpression(string label, string source, SourceSpan expected)
        => AssertEveryPathReportsAtTheUnaryExpression<EvalError.TypeMismatch>(label, source, expected);

    private static async Task AssertEveryPathReportsAtTheUnaryExpression<TError>(string label, string source, SourceSpan expected)
        where TError : EvalError
    {
        Assert.False(string.IsNullOrEmpty(label));
        var ast = Program(source);

        var plain = Evaluator.Run(ast);
        Assert.True(plain.IsError);
        Assert.Equal(expected, Assert.IsType<TError>(Innermost(plain.Error)).Span);

        var counted = Evaluator.RunCounted(ast);
        Assert.True(counted.IsError);
        Assert.Equal(expected, Assert.IsType<TError>(Innermost(counted.Error)).Span);

        // The async twin completes synchronously through the pass-through seam and
        // must report the identical structured error.
        var twin = Evaluator.RunCountedAsync(ast, new PassThroughAsyncZeroArgPropertyResultCache());
        Assert.True(twin.IsCompleted);
        var twinResult = await twin;
        Assert.True(twinResult.IsError);
        Assert.Equal(expected, Assert.IsType<TError>(Innermost(twinResult.Error)).Span);
        Assert.Equal(
            LoopDiagnosticParityAssertions.DescribeErrorTree(counted.Error),
            LoopDiagnosticParityAssertions.DescribeErrorTree(twinResult.Error));
    }

    [Fact]
    public void Engine_ProjectsTheUnaryExpressionSpanAndKeepsTheErrorFamily()
    {
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run("-(1, 2)"));
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.ArityMismatch, error.Code);
        Assert.False(error.IsResourceLimit);
        Assert.Equal(new SourceSpan(1, 1, 1, 8), error.Span);

        var notFailure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run("X = ()\nnot X"));
        var notError = Assert.Single(notFailure.Errors);
        Assert.Equal(KatLangErrorCode.TypeMismatch, notError.Code);
        Assert.False(notError.IsResourceLimit);
        Assert.Equal(new SourceSpan(2, 1, 2, 6), notError.Span);
        Assert.Contains("operator `not` expects a Boolean operand", notError.Message);
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
    [InlineData("not (false)", "true")]
    [InlineData("not (1 > 2)", "true")]
    [InlineData("-((3))", "-3")]
    [InlineData("-(1) + 4", "3")]
    [InlineData("X = (3)\n-X", "-3")]
    [InlineData("X = (true)\nnot X", "false")]
    public void ValidUnaryOperands_EvaluateUnchanged(string source, string expected)
    {
        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));
        Assert.Equal(expected, success.ToDisplayString());
    }
}
