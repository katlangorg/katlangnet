namespace KatLang.Tests;

/// <summary>
/// F6: parentheses that merely group an expression are the syntactic expression the
/// surrounding construct consumes, so an expression the parser unwraps from
/// redundant grouping keeps the group's FULL written extent as its source span —
/// `(1)` is located as `(1)`, never merely as `1` — and nested redundant groups
/// accumulate their outer extent. Only the span changes: AST shape, grouping
/// semantics, arity normalization, and evaluation are untouched, and the children
/// of the unwrapped node keep their own spans.
/// </summary>
public class GroupedExpressionSpanTests
{
    private static Expr SingleRow(string source)
    {
        var raw = Parser.ParseSyntax(source);
        Assert.False(raw.HasErrors, string.Join(Environment.NewLine, raw.Diagnostics.Select(d => d.Message)));
        return Assert.Single(raw.Root.Output);
    }

    [Theory]
    [InlineData("(1)", 1, 4)]
    [InlineData("((1))", 1, 6)]
    [InlineData("( 1 )", 1, 6)]
    [InlineData("(((1)))", 1, 8)]
    public void UnwrappedLiteral_SpansTheWholeGroup(string source, int startColumn, int endColumn)
    {
        var row = Assert.IsType<Expr.Num>(SingleRow(source));
        Assert.Equal(1, row.Value);
        Assert.Equal(new SourceSpan(1, startColumn, 1, endColumn), row.Span);
    }

    [Fact]
    public void UnwrappedCompoundExpressions_SpanTheWholeGroup_ChildrenKeepTheirs()
    {
        var binary = Assert.IsType<Expr.Binary>(SingleRow("(1 + 2)"));
        Assert.Equal(new SourceSpan(1, 1, 1, 8), binary.Span);
        Assert.Equal(new SourceSpan(1, 2, 1, 3), binary.Left.Span);
        Assert.Equal(new SourceSpan(1, 6, 1, 7), binary.Right.Span);

        var call = Assert.IsType<Expr.Call>(SingleRow("(F(1))"));
        Assert.Equal(new SourceSpan(1, 1, 1, 7), call.Span);
        Assert.Equal(new SourceSpan(1, 2, 1, 3), call.Function.Span);
        Assert.Equal(new SourceSpan(1, 4, 1, 5), Assert.Single(call.Args).Span);

        var dot = Assert.IsType<Expr.DotCall>(SingleRow("(a.b)"));
        Assert.Equal(new SourceSpan(1, 1, 1, 6), dot.Span);
        Assert.Equal(new SourceSpan(1, 2, 1, 3), dot.Target.Span);
        Assert.Equal(new SourceSpan(1, 4, 1, 5), dot.MemberSpan);

        var unary = Assert.IsType<Expr.Unary>(SingleRow("(-1)"));
        Assert.Equal(new SourceSpan(1, 1, 1, 5), unary.Span);
        Assert.Equal(new SourceSpan(1, 3, 1, 4), unary.Operand.Span);

        var block = Assert.IsType<Expr.AlgorithmExpr>(SingleRow("({ 1 })"));
        Assert.Equal(new SourceSpan(1, 1, 1, 8), block.Span);

        var list = Assert.IsType<Expr.ListLiteral>(SingleRow("([1])"));
        Assert.Equal(new SourceSpan(1, 1, 1, 6), list.Span);
        Assert.Equal(new SourceSpan(1, 3, 1, 4), Assert.Single(list.Items).Span);

        var text = Assert.IsType<Expr.StringLiteral>(SingleRow("('a')"));
        Assert.Equal(new SourceSpan(1, 1, 1, 6), text.Span);
    }

    [Fact]
    public void MultiLineGroup_SpansFromTheOpeningToTheClosingParenthesis()
    {
        var binary = Assert.IsType<Expr.Binary>(SingleRow("(1 +\n  2)"));
        Assert.Equal(new SourceSpan(1, 1, 2, 5), binary.Span);
    }

    [Fact]
    public void SurvivingCaptureLayers_AreUnchanged()
    {
        // A reference keeps its capture layer (`(x)`) and a group of several slots is
        // a capture: both already spanned their parentheses, and the inner nodes keep
        // their own spans exactly as before.
        var capture = Assert.IsType<Expr.Capture>(SingleRow("(x)"));
        Assert.Equal(new SourceSpan(1, 1, 1, 4), capture.Span);
        Assert.Equal(new SourceSpan(1, 2, 1, 3), Assert.Single(capture.Body).Span);

        var pair = Assert.IsType<Expr.Capture>(SingleRow("(1, 2)"));
        Assert.Equal(new SourceSpan(1, 1, 1, 7), pair.Span);
        Assert.Equal(new SourceSpan(1, 2, 1, 3), pair.Body[0].Span);
        Assert.Equal(new SourceSpan(1, 5, 1, 6), pair.Body[1].Span);

        var nestedPair = Assert.IsType<Expr.Capture>(SingleRow("((1, 2))"));
        Assert.Equal(new SourceSpan(1, 1, 1, 9), nestedPair.Span);
        Assert.Equal(new SourceSpan(1, 2, 1, 8), Assert.IsType<Expr.Capture>(Assert.Single(nestedPair.Body)).Span);

        var empty = Assert.IsType<Expr.EmptySequence>(SingleRow("(())"));
        Assert.Equal(new SourceSpan(1, 1, 1, 5), empty.Span);
    }

    [Fact]
    public void GroupedOperand_LocatesTheEnclosingExpressionFromTheParenthesis()
    {
        // `(1) + 'a'`: the binary expression starts at the group, so its operand
        // failure is located from column 1 — not from the inner `1` at column 2.
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run("(1) + 'a'"));
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.TypeMismatch, error.Code);
        Assert.Equal(new SourceSpan(1, 1, 1, 10), error.Span);

        var nested = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run("((1)) + 'a'"));
        var nestedError = Assert.Single(nested.Errors);
        Assert.Equal(KatLangErrorCode.TypeMismatch, nestedError.Code);
        Assert.Equal(new SourceSpan(1, 1, 1, 12), nestedError.Span);
    }

    [Fact]
    public void UnaryOnAGroup_LocatesTheUnaryFromItsOperator()
    {
        // `-(1, 2)`: the group is the unary's operand, so the unary expression — and
        // its BadArity (F5) — spans from the operator through the closing parenthesis.
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run("-(1, 2)"));
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.ArityMismatch, error.Code);
        Assert.Equal(new SourceSpan(1, 1, 1, 8), error.Span);
    }

    [Theory]
    [InlineData("(1) + 2", "3")]
    [InlineData("((2)) * 3", "6")]
    [InlineData("(1, 2).count", "2")]
    [InlineData("F(x) = x * 2\n(F(3))", "6")]
    [InlineData("(-(1)) + 4", "3")]
    [InlineData("(1)", "1")]
    [InlineData("((1))", "1")]
    [InlineData("(())", "()")]
    public void GroupedExpressions_EvaluateUnchanged(string source, string expected)
    {
        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));
        Assert.Equal(expected, success.ToDisplayString());
    }

    [Fact]
    public void RedundantGrouping_DoesNotResetTheExpressionChainGuard()
    {
        // The chain guard counts operator/postfix depth by node reference; the
        // re-spanned copy of an unwrapped chain inherits its registered depth, so
        // wrapping a maximal chain in parentheses cannot buy another level.
        var maximal = string.Join(" + ", Enumerable.Repeat("1", Parser.MaxExpressionChainDepth + 1));
        Assert.False(Parser.ParseSyntax(maximal).HasErrors);
        Assert.False(Parser.ParseSyntax("(" + maximal + ")").HasErrors);

        Assert.Contains(
            Parser.ParseSyntax(maximal + " + 1").Diagnostics,
            d => d.Code == DiagnosticCode.ExpressionChainTooDeep);
        Assert.Contains(
            Parser.ParseSyntax("(" + maximal + ") + 1").Diagnostics,
            d => d.Code == DiagnosticCode.ExpressionChainTooDeep);
    }

    [Theory]
    [InlineData(1)]
    [InlineData(2)]
    [InlineData(4)]
    public void RepeatedGrouping_PreservesTheExactRemainingChainBudget(int layers)
    {
        // Group both a binary spine and a postfix spine below the boundary, then
        // spend exactly the remaining depth. Neither lost nor doubled registration
        // can satisfy both the admission and rejection assertions.
        foreach (var postfix in new[] { false, true })
        {
            var suffix = postfix ? ".string" : " + 1";
            var prefix = "1" + string.Concat(Enumerable.Repeat(suffix, Parser.MaxExpressionChainDepth - 2));
            var grouped = new string('(', layers) + prefix + new string(')', layers);
            Assert.False(Parser.ParseSyntax(grouped + suffix + suffix).HasErrors);
            Assert.Contains(Parser.ParseSyntax(grouped + suffix + suffix + suffix).Diagnostics,
                diagnostic => diagnostic.Code == DiagnosticCode.ExpressionChainTooDeep);
        }
    }

    [Fact]
    public void GroupedCall_NavigationStillLocatesOnlyTheWrittenIdentifier()
    {
        const string source = "F(x) = x\n((F(1))).string";
        var parsed = SourceProvenance.ParseValid(source);
        var edge = Assert.IsType<Expr.DotCall>(parsed.Root.Output[0]);
        Assert.Equal(new SourceSpan(2, 1, 2, 9), edge.Target.Span);
        var model = KatLang.Semantics.SemanticModelBuilder.Build(parsed.Root);
        var reference = model.FindResolutionAt(new SourcePosition(2, 3))!;
        Assert.Equal(KatLang.Semantics.IdentifierClassification.PropertyReference, reference.Classification);
        Assert.Equal(new SourceSpan(1, 1, 1, 2), reference.ResolvedDeclaration!.Span);
        Assert.Null(model.FindResolutionAt(new SourcePosition(2, 1)));
        Assert.Null(model.FindResolutionAt(new SourcePosition(2, 2)));
    }
}
