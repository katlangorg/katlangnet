using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// POSTFIX SELECTION SYNTAX (October 2026; <c>syntax.md</c> § Postfix selection). A <c>[</c> on the
/// same physical line as the receiver's final token (same-line spaces and tabs allowed) opens the
/// selector list of a postfix selection over any completed postfix-level expression; the list is the
/// list literal's expression-list production (zero or more slots, whole-slot spreads, multiline once
/// open). A <c>[</c> on a later line begins a new list literal. Commas select siblings, chained
/// brackets descend, selection has postfix precedence, a selection is never a call target, and the
/// star disambiguation is unchanged. The colon form is retired: <c>expr:selector</c> is
/// <see cref="DiagnosticCode.RetiredColonSelection"/>, recovered as the selection it meant.
/// </summary>
public class PostfixSelectionSyntaxTests
{
    private static Expr SingleRow(string source)
        => Assert.Single(SourceProvenance.ParseSyntaxValidRoot(source).Output);

    // A fragment can end in spread only inside an explicitly closed slot.
    // The real control remains in the parsed program and is asserted here.
    private static Expr CommaClosedSlot(string fragment)
    {
        var root = SourceProvenance.ParseSyntaxValidRoot(fragment + ", 997");
        Assert.Equal(2, root.Output.Count);
        Assert.Equal(997m, Assert.IsType<Expr.Num>(root.Output[1]).Value);
        return root.Output[0];
    }

    private static string Shape(Expr expr) => expr switch
    {
        Expr.Index index => $"sel({Shape(index.Target)}; {string.Join(", ", index.Selectors.Select(Shape))})",
        Expr.SequenceSpread spread => $"{Shape(spread.Operand)}*",
        Expr.Resolve resolve => resolve.Name,
        Expr.Num num => num.Value.ToString(),
        Expr.ListLiteral list => $"[{string.Join(", ", list.Items.Select(Shape))}]",
        Expr.Capture capture => $"({string.Join(", ", capture.Body.Select(Shape))})",
        Expr.EmptySequence => "()",
        Expr.Unary unary => $"{unary.Op}({Shape(unary.Operand)})",
        Expr.Binary binary => $"{binary.Op}({Shape(binary.Left)}, {Shape(binary.Right)})",
        Expr.Call call => $"call({Shape(call.Function)}; {string.Join(", ", call.Args.Select(Shape))})",
        Expr.DotCall dot => dot.Args is null ? $"dot({Shape(dot.Target)}.{dot.Name})" : $"dot({Shape(dot.Target)}.{dot.Name}; {string.Join(", ", dot.Args.Select(Shape))})",
        Expr.StringLiteral text => $"'{text.Value}'",
        Expr.Grace grace => $"grace({Shape(grace.Inner)})",
        Expr.AlgorithmExpr => "{...}",
        _ => $"<{expr.GetType().Name}>",
    };

    // ── Shapes ───────────────────────────────────────────────────────────────

    [Theory]
    [InlineData("Data[]", "sel(Data; )")]
    [InlineData("Data[0]", "sel(Data; 0)")]
    [InlineData("Data[0, 1]", "sel(Data; 0, 1)")]
    [InlineData("Data[2, 0, 2]", "sel(Data; 2, 0, 2)")]
    [InlineData("Data[Is*]", "sel(Data; Is*)")]
    [InlineData("Data[0, Is*, 1]", "sel(Data; 0, Is*, 1)")]
    [InlineData("Data[(0, 1)]", "sel(Data; (0, 1))")]
    [InlineData("Data[(0)]", "sel(Data; 0)")]
    [InlineData("Data[[0, 1]*]", "sel(Data; [0, 1]*)")]
    [InlineData("Data[i + 1]", "sel(Data; Add(i, 1))")]
    [InlineData("Data[-1]", "sel(Data; Minus(1))")]
    public void TheSelectorList_IsAnOrdinaryExpressionList(string row, string expected)
        => Assert.Equal(expected, Shape(SingleRow(row)));

    [Theory]
    [InlineData("Data [0]")]
    [InlineData("Data\t[0]")]
    [InlineData("Data  [0]")]
    [InlineData("Data [ 0 ]")]
    [InlineData("Data [\n  0\n]")]
    [InlineData("Data[ # comment\n  0\n]")]
    public void SameLineWhitespaceBeforeTheBracket_AndMultilineContents_AreOneSelection(string row)
        => Assert.Equal("sel(Data; 0)", Shape(SingleRow(row)));

    [Fact]
    public void ATrailingComma_IsRejected_ExactlyLikeInAListLiteral()
    {
        var list = Parser.ParseSyntax("[\n  0,\n]").Diagnostics.Select(d => (d.Code, d.Message, d.Span)).ToArray();
        var selection = Parser.ParseSyntax("Data[\n  0,\n]").Diagnostics.Select(d => (d.Code, d.Message, d.Span)).ToArray();
        Assert.NotEmpty(list);
        Assert.Equal(list, selection);
    }

    [Fact]
    public void MultilineContents_SeparateSelectorsLikeAListLiteral()
        => Assert.Equal("sel(Data; 0, 1)", Shape(SingleRow("Data [\n    0,\n    1\n]")));

    [Theory]
    [InlineData("Data\n[0, 1]")]
    [InlineData("Data # note\n[0, 1]")]
    [InlineData("Grid[0]\n[1]")]
    public void ABracketOnALaterLine_IsANewListRow_NeverASelection(string source)
    {
        var root = SourceProvenance.ParseSyntaxValidRoot(source);
        Assert.Equal(2, root.Output.Count);
        Assert.IsType<Expr.ListLiteral>(root.Output[1]);
    }

    [Theory]
    [InlineData("Grid[0][1]", "sel(sel(Grid; 0); 1)")]
    [InlineData("Grid [0] [1]", "sel(sel(Grid; 0); 1)")]
    [InlineData("Grid[0, 1]", "sel(Grid; 0, 1)")]
    [InlineData("Data()[0]", "sel(call(Data; ); 0)")]
    [InlineData("(Data)[0]", "sel(Data; 0)")]
    [InlineData("((Data))[0]", "sel(Data; 0)")]
    [InlineData("[10, 20][0]", "sel([10, 20]; 0)")]
    [InlineData("(10, 20)[0]", "sel((10, 20); 0)")]
    [InlineData("5[0]", "sel(5; 0)")]
    [InlineData("'abc'[0]", "sel('abc'; 0)")]
    [InlineData("A.B[0]", "sel(dot(A.B); 0)")]
    [InlineData("A[0].B", "dot(sel(A; 0).B)")]
    [InlineData("BuildData(n)[0].sum", "dot(sel(call(BuildData; n); 0).sum)")]
    [InlineData("-A[0]", "Minus(sel(A; 0))")]
    [InlineData("A[0] ^ 2", "Pow(sel(A; 0), 2)")]
    [InlineData("2 ^ A[0]", "Pow(2, sel(A; 0))")]
    [InlineData("(A*)[0]", "sel((A*); 0)")]
    [InlineData("A[0]*", "sel(A; 0)*")]
    public void SelectionComposes_AsAPostfixForm(string row, string expected)
        => Assert.Equal(expected, Shape(CommaClosedSlot(row)));

    [Theory]
    [InlineData("A*[0]")]
    [InlineData("A *[0]")]
    [InlineData("A*\n[0]")]
    public void AStarBeforeABracket_IsMultiplication(string row)
        => Assert.Equal("Mul(A, [0])", Shape(SingleRow(row)));

    [Theory]
    [InlineData("A[0](1)", "1:5")]
    [InlineData("A[0] {1}", "1:6")]
    [InlineData("Data[0 1]", "1:8")]
    public void ASelection_IsNeverACallTarget_AndSlotsNeedCommas(string row, string itemStart)
    {
        var diagnostic = Assert.Single(SourceProvenance.ExpectFrontEndError(row));
        Assert.Equal(DiagnosticCode.UnseparatedSameLineItem, diagnostic.Code);
        Assert.Equal(itemStart, $"{diagnostic.Span!.Value.Start.Line}:{diagnostic.Span!.Value.Start.Column}");
    }

    // ── Spans ────────────────────────────────────────────────────────────────

    [Fact]
    public void TheSelectionSpan_RunsFromTheReceiverThroughTheClosingBracket()
    {
        var selection = Assert.IsType<Expr.Index>(SingleRow("Data [0,\n  1]"));
        Assert.Equal(new SourceSpan(1, 1, 2, 5), selection.Span);
        Assert.Equal(new SourceSpan(1, 7, 1, 8), selection.Selectors[0].Span);
        Assert.Equal(new SourceSpan(2, 3, 2, 4), selection.Selectors[1].Span);
    }

    [Fact]
    public void ASelectorFailure_IsPositionedAtItsWrittenSlot()
    {
        var result = KatLangEngine.Run("Data = [10, 20]\nData[0, 99, 1]");
        var failure = Assert.IsType<RunResult.EvalFailure>(result);
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.BadIndex, error.Code);
        Assert.Equal(new SourceSpan(2, 9, 2, 11), error.Span);
    }

    // ── Malformed brackets: delimiter ownership and recovery ─────────────────

    [Theory]
    [InlineData("Data = [1]\nData[0\nB = 1\nB")]
    [InlineData("Data = [1]\nData[0)\nB = 1\nB")]
    [InlineData("Data = [1]\nF(x) = x\nF(Data[0)\nB = 1\nB")]
    [InlineData("Data = [1]\nData[\nB = 1\nB")]
    [InlineData("Data = [1]\nData[0,\nB = 1\nB")]
    public void AMalformedSelectorList_RecoversWithoutSwallowingLaterDeclarations(string source)
    {
        var parsed = SourceProvenance.ParseAllowingDiagnostics(source).Parsed;
        Assert.True(parsed.HasErrors);
        Assert.Contains(parsed.Root.Properties, static property => property.Name == "B");
    }

    // ── The retired colon form ───────────────────────────────────────────────

    [Theory]
    [InlineData("Data = [1]\nData:0", "2:5", "2:7", "sel(Data; 0)")]
    [InlineData("Data = [1]\nData : 0", "2:6", "2:9", "sel(Data; 0)")]
    [InlineData("Data = [1]\nData:(0)", "2:5", "2:9", "sel(Data; 0)")]
    [InlineData("Grid = [[1]]\nGrid:0:0", "2:5", "2:7", "sel(sel(Grid; 0); 0)")]
    [InlineData("Data = [1]\nData():0", "2:7", "2:9", "sel(call(Data; ); 0)")]
    public void TheRetiredColonForm_ReportsTheMigrationDiagnostic_AndRecoversAsTheSelectionItMeant(
        string source, string start, string end, string recoveredShape)
    {
        var parsed = SourceProvenance.ParseAllowingDiagnostics(source).Parsed;
        Assert.All(parsed.Diagnostics, static d => Assert.Equal(DiagnosticCode.RetiredColonSelection, d.Code));
        var first = parsed.Diagnostics[0];
        Assert.Equal(start, $"{first.Span!.Value.Start.Line}:{first.Span!.Value.Start.Column}");
        Assert.Equal(end, $"{first.Span!.Value.End.Line}:{first.Span!.Value.End.Column}");
        Assert.Contains("postfix brackets", first.Message, StringComparison.Ordinal);
        var raw = SourceProvenance.ParseSyntaxAllowingDiagnosticsRoot(source);
        Assert.Equal(recoveredShape, Shape(raw.Output[0]));
    }

    [Fact]
    public void ARetiredColonWithAPrefixGraceSelector_RecoversAsTheGracedSelection()
    {
        // `~i` was an ordinary selector primary of the colon form, so `xs:~i` recovers as `xs[~i]`
        // with the one migration diagnostic — never a second, cascading Grace report.
        const string source = "K = xs:~i\nK(1, [10, 20])";
        var parsed = SourceProvenance.ParseAllowingDiagnostics(source).Parsed;
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticCode.RetiredColonSelection, diagnostic.Code);
        var raw = SourceProvenance.ParseSyntaxAllowingDiagnosticsRoot(source);
        var body = Assert.IsType<Algorithm.User>(Assert.Single(raw.Properties).Value);
        Assert.Equal("sel(xs; grace(i))", Shape(Assert.Single(body.Output)));
    }

    [Theory]
    [InlineData("x = (1, 2)\nx:-1")]
    [InlineData("Pair = (1, 2)\nPair:\nGood = 41\nGood")]
    [InlineData("Pair = (1, 2)\nP = Pair\n:0\nP")]
    public void ARetiredColonWithoutASelector_ReportsOnlyTheMigrationDiagnostic(string source)
    {
        var parsed = SourceProvenance.ParseAllowingDiagnostics(source).Parsed;
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticCode.RetiredColonSelection, diagnostic.Code);
    }

    [Fact]
    public void TheRetiredColonDiagnostic_MapsToItsPublicErrorCode()
    {
        var result = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run("Data = [1]\nData:0"));
        Assert.Equal(KatLangErrorCode.RetiredColonSelection, Assert.Single(result.Errors).Code);
    }

    [Fact]
    public void AHoleLevelColon_StaysTheHolesOwnDiagnostic_WhileBracketSelectionWorksInAHole()
    {
        var diagnostic = Assert.Single(SourceProvenance.ExpectFrontEndError("xs = [1]\n\"{xs:0}\""));
        Assert.Equal(DiagnosticCode.InvalidInterpolationHole, diagnostic.Code);
        Assert.Contains("\"{xs[0]}\"", diagnostic.Message, StringComparison.Ordinal);
        Assert.Equal("1, 2 and ()", KatLangEngine.Run("xs = [1, 2]\n\"{xs[0]}, {xs[1]} and {xs[]}\"").ToDisplayString().Trim('\''));
        Assert.Equal("(2, 1)", KatLangEngine.Run("xs = [1, 2]\n\"{xs[1, 0]}\"").ToDisplayString().Trim('\''));
    }

    // ── Elaboration: inference, Grace, lifting, open ─────────────────────────

    [Theory]
    [InlineData("K = xs[i]\nK([10, 20], 1)", "20")]
    [InlineData("K = xs[i, j]\nK([10, 20], 1, 0)", "(20, 10)")]
    [InlineData("K = xs[is*]\nK([10, 20], [1, 0])", "(20, 10)")]
    [InlineData("K = xs[~i]\nK(1, [10, 20])", "20")]
    [InlineData("Inc(x) = x + 1\nG = [10, 20, 30][Inc]\nG(1)", "30")]
    public void SelectorNames_AreInferredInFirstOccurrenceOrder_AndLiftAsValues(string source, string expected)
    {
        SourceProvenance.ParseValid(source);
        Assert.Equal(expected, KatLangEngine.Run(source).ToDisplayString());
    }

    [Fact]
    public void ASelection_IsNotAnOpenForm()
    {
        // `open` comes first, so the only possible rejection is the target's own form: a selection
        // is a value, never an open form (BadOpenForm at the target), and no placement error masks it.
        var diagnostics = SourceProvenance.ExpectFrontEndError("open A[0]\nA = { public X = 1 }\nX");
        var badForm = Assert.Single(diagnostics, static d => d.Code == DiagnosticCode.BadOpenForm);
        Assert.Equal(1, badForm.Span!.Value.Start.Line);
        Assert.Equal(6, badForm.Span!.Value.Start.Column);
        Assert.DoesNotContain(diagnostics, static d => d.Code == DiagnosticCode.InvalidOpenDeclaration);
    }

    [Fact]
    public void ListPatternsInClauseHeads_AreUnchanged()
        => Assert.Equal("3", KatLangEngine.Run("F([x, y]) = x + y\nF([1, 2])").ToDisplayString());

    // ── Editor semantics ─────────────────────────────────────────────────────

    [Fact]
    public void NamesInsideSelectors_ResolveToTheirDeclarations()
    {
        const string source = "Data = [10, 20]\ni = 1\nData[i, 0]";
        var model = SemanticModelBuilder.Build(SourceProvenance.ParseValid(source).Parsed);
        var receiver = model.FindResolutionAt(new SourcePosition(3, 1));
        Assert.Equal("Data", receiver?.ResolvedProperty?.Name);
        var selector = model.FindResolutionAt(new SourcePosition(3, 6));
        Assert.Equal("i", selector?.ResolvedProperty?.Name);
        Assert.Equal(new SourceSpan(2, 1, 2, 2), selector!.ResolvedDeclaration!.Span);
    }

    // ── Budgets: chain depth and nesting ─────────────────────────────────────

    [Fact]
    public void AChainOfSelections_UsesTheExpressionChainBudget()
    {
        var within = "A = 1\nA" + string.Concat(Enumerable.Repeat("[0]", Parser.MaxExpressionChainDepth - 1));
        Assert.False(Parser.ParseSyntax(within).HasErrors);
        var beyond = "A = 1\nA" + string.Concat(Enumerable.Repeat("[0]", Parser.MaxExpressionChainDepth + 1));
        Assert.Contains(Parser.ParseSyntax(beyond).Diagnostics, static d => d.Code == DiagnosticCode.ExpressionChainTooDeep);
    }

    [Fact]
    public void NestedSelectorLists_StayWithinTheParserBudgetAndEvaluate()
    {
        var source = "A = [0]\n" + string.Concat(Enumerable.Repeat("A[", 40)) + "0" + new string(']', 40);
        Assert.Equal("0", KatLangEngine.Run(source).ToDisplayString());
    }
}
