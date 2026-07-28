namespace KatLang.Tests;

/// <summary>
/// Surface-syntax coverage for the collecting-binding marker: postfix
/// <c>name...</c> is the ONLY collecting-binding spelling and is valid only in
/// binding positions. The ellipsis token is not an expression operator, and a
/// prefix ellipsis never declares a collecting binding. Expression spreading
/// is the named intrinsic (<c>spread(expr)</c> / <c>expr.spread</c>), covered
/// in depth by <see cref="SpreadIntrinsicSyntaxTests"/>.
/// </summary>
public class CollectingBindingSyntaxTests
{
    private static string Display(string source)
    {
        var result = KatLangEngine.Run(source);
        Assert.True(result is RunResult.Success, $"Expected success but got: {result.ToDisplayString()}");
        return result.ToDisplayString();
    }

    [Fact]
    public void PostfixCollectingBinding_CollectsEmptySingletonAndMultipleArgumentsAsExactLists()
    {
        Assert.Equal("[]", Display("F(items...) = items\nF()"));
        Assert.Equal("[1]", Display("F(items...) = items\nF(1)"));
        Assert.Equal("[1, 2, 3]", Display("F(items...) = items\nF(1, 2, 3)"));
    }

    [Fact]
    public void PostfixCollectingBinding_SupportsSumAndMovableMiddle()
    {
        Assert.Equal("6", Display("Sum(items...) = items.sum\nSum(1, 2, 3)"));
        Assert.Equal(
            "[2, 3, 4]",
            Display("Middle(first, middle..., last) = middle\nMiddle(1, 2, 3, 4, 5)"));
    }

    [Fact]
    public void PostfixCollectingBinding_SupportsFrontMiddleAndFinalPositions()
    {
        Assert.Equal("[1, 2]", Display("F(prefix..., last) = prefix\nF(1, 2, 3)"));
        Assert.Equal("[2, 3]", Display("F(first, middle..., last) = middle\nF(1, 2, 3, 4)"));
        Assert.Equal("[2, 3]", Display("F(first, suffix...) = suffix\nF(1, 2, 3)"));
    }

    [Fact]
    public void PostfixCollectingDeconstruction_CollectsMovableMiddleAsExactList()
        => Assert.Equal(
            "(1, [2, 3, 4], 5)",
            Display(
                """
                first, middle..., last = 1, 2, 3, 4, 5
                (first, middle, last)
                """));

    [Theory]
    [InlineData("Forward(items...) = Target(spread(items))")]
    [InlineData("Forward(items...) = Target(items.spread)")]
    public void Forwarding_UsesCollectingBindingAndNamedSpreadAsOppositeOperations(string forward)
        => Assert.Equal(
            "[1, 2, 3]",
            Display(
                $$"""
                Target(items...) = items
                {{forward}}
                Forward(1, 2, 3)
                """));

    [Theory]
    [InlineData("F([1, 2])", "[[1, 2]]")]
    [InlineData("F(spread([1, 2]))", "[1, 2]")]
    [InlineData("F([1, 2].spread)", "[1, 2]")]
    [InlineData("F((1, 2))", "[(1, 2)]")]
    [InlineData("F(spread((1, 2)))", "[1, 2]")]
    [InlineData("F((1, 2).spread)", "[1, 2]")]
    [InlineData("F([])", "[[]]")]
    [InlineData("F(spread([]))", "[]")]
    [InlineData("F([].spread)", "[]")]
    [InlineData("F(())", "[()]")]
    [InlineData("F(spread(()))", "[]")]
    [InlineData("F(().spread)", "[]")]
    public void PostfixCollectingBinding_PreservesExistingListAndSequenceArgumentBoundaries(
        string call,
        string expected)
        => Assert.Equal(expected, Display($"F(items...) = items\n{call}"));

    /// <summary>
    /// The central orientation test: ONE source containing both the postfix
    /// collecting marker and a named spread, proving the marker elaborates to
    /// a collecting binding and the named form to a spread expression, and
    /// that neither is mistaken for the other.
    /// </summary>
    [Fact]
    public void PostfixIsACollectingBindingAndNamedSpreadIsASpread_InTheSameDeclaration()
    {
        const string source =
            """
            Target(items...) = items
            Forward(items...) = Target(spread(items))
            Forward(1, 2, 3)
            """;

        var parse = Parser.Parse(source);
        Assert.Empty(parse.Diagnostics);

        var forward = Assert.Single(parse.Root.Properties, property => property.Name == "Forward").Value;

        // Left `items...`: a collecting binding carrying the source-backed marker span.
        var parameter = Assert.Single(forward.Parameters);
        Assert.Equal(ParameterKind.Variadic, parameter.Kind);
        Assert.Equal("items...", parameter.DisplayName);
        Assert.Equal(new SourceSpan(2, 14, 2, 16), parameter.CollectingMarkerSpan);

        // Right `spread(items)`: a spread expression over the bound variadic parameter, not a binding.
        var call = Assert.IsType<Expr.Call>(Assert.Single(forward.Output));
        var spread = Assert.IsType<Expr.SequenceSpread>(Assert.Single(call.Args.Output));
        Assert.Equal("items", Assert.IsType<Expr.Param>(spread.Operand).Name);

        Assert.Equal("[1, 2, 3]", Display(source));
    }

    [Theory]
    [InlineData("F(...items) = items", "items", 3, 10)]
    [InlineData("F(first, ...middle, last) = middle", "middle", 10, 18)]
    [InlineData("F(...items, last) = items", "items", 3, 10)]
    [InlineData("F(first, ...items) = items", "items", 10, 17)]
    public void PrefixSpellingInParameterPattern_IsRejectedAndStaysAFixedBinding(
        string source,
        string name,
        int startColumn,
        int endColumn)
    {
        var syntax = Parser.ParseSyntax(source);
        var parse = Parser.Parse(source);

        Assert.True(syntax.HasErrors);
        Assert.True(parse.HasErrors);
        var error = Assert.Single(parse.Diagnostics);
        Assert.Equal(DiagnosticSeverity.Error, error.Severity);
        Assert.Equal(
            $"Prefix `...` cannot declare a collecting binding. Write `{name}...` instead of `...{name}`.",
            error.Message);
        Assert.Equal(new SourceSpan(1, startColumn, 1, endColumn), error.Span);

        // A clean break: nothing is accepted with a warning.
        Assert.DoesNotContain(parse.Diagnostics, static diagnostic =>
            diagnostic.Severity == DiagnosticSeverity.Warning);

        AssertNoVariadicBindings(syntax.Root);
        AssertNoVariadicBindings(parse.Root);
    }

    [Theory]
    [InlineData("...items = values")]
    [InlineData("first, ...middle, last = values")]
    [InlineData("...items, last = values")]
    [InlineData("first, ...items = values")]
    [InlineData("first, middle......, last = 1, 2, 3")]
    public void InvalidEllipsisShapesInDeconstructionPosition_FailAsOrdinaryInvalidSyntax(
        string source)
    {
        // Only valid binding shapes (identifier with at most one same-line
        // postfix marker) are recognized as deconstruction targets. Anything
        // else is never claimed as a binding pattern and fails through
        // ordinary unexpected-token handling — with no warning and no
        // collecting binding in the recovered tree.
        var syntax = Parser.ParseSyntax(source);
        var parse = Parser.Parse(source);

        Assert.True(syntax.HasErrors);
        Assert.True(parse.HasErrors);
        Assert.Contains(parse.Diagnostics, static diagnostic =>
            diagnostic.Message.Contains("Unexpected token: 'Ellipsis'", StringComparison.Ordinal));
        Assert.All(parse.Diagnostics, static diagnostic =>
            Assert.Equal(DiagnosticSeverity.Error, diagnostic.Severity));

        AssertNoVariadicBindings(syntax.Root);
        AssertNoVariadicBindings(parse.Root);
    }

    [Fact]
    public void StrayEllipsisBeforeAValidDeconstruction_RecoversTheValidRemainder()
    {
        // The stray prefix `...` fails as an ordinary unexpected token and is
        // never itself a binding; the remainder `middle..., last = values` is
        // ordinary valid syntax and still parses as a collecting
        // deconstruction — recovery reaches later valid declarations.
        var parse = Parser.Parse("first, ...middle..., last = values");

        Assert.True(parse.HasErrors);
        Assert.Contains(parse.Diagnostics, static diagnostic =>
            diagnostic.Message.Contains("Unexpected token: 'Ellipsis'", StringComparison.Ordinal));
        Assert.Contains(parse.Root.Properties, static property => property.Name == "middle");
        Assert.Contains(parse.Root.Properties, static property => property.Name == "last");
    }

    [Theory]
    [InlineData("F(items...) = items\nA = 1, 2\nF(spread(A))")]
    [InlineData("F(items...) = items\nF(spread([1, 2]))")]
    [InlineData("F(items...) = items\nF([1, 2].spread)")]
    [InlineData("Values = 1, 2, 3\nfirst, middle..., last = spread(Values)\nmiddle")]
    [InlineData("Values = 1, 2, 3\nfirst, middle..., last = Values.spread\nmiddle")]
    public void NamedSpread_RemainsValidBesideCollectingBindings(string source)
        => Assert.Empty(Parser.Parse(source).Diagnostics);

    [Theory]
    [InlineData("F(a..., b...) = a", "Only one collecting binding")]
    [InlineData("a..., b... = 1, 2", "at most one collecting binding")]
    [InlineData("F(items......) = items", "Malformed collecting binding")]
    [InlineData("first, middle......, last = 1, 2, 3", "Unexpected token: 'Ellipsis'")]
    [InlineData("F(...a, b...) = a", "cannot declare a collecting binding")]
    [InlineData("F(a..., ...b) = b", "cannot declare a collecting binding")]
    [InlineData("F(...items...) = items", "Malformed collecting binding")]
    public void MalformedCollectingForms_FailSafelyWithAnErrorDiagnostic(
        string source,
        string expectedFragment)
    {
        var parse = Parser.Parse(source);

        Assert.True(parse.HasErrors);
        Assert.Contains(
            parse.Diagnostics,
            diagnostic => diagnostic.Message.Contains(expectedFragment, StringComparison.Ordinal));
        Assert.DoesNotContain(parse.Diagnostics, static diagnostic =>
            diagnostic.Severity == DiagnosticSeverity.Warning);
    }

    [Theory]
    [InlineData("F(...) = 0")]
    [InlineData("F(...1) = 0")]
    [InlineData("F(...items...) = items")]
    [InlineData("F(items......) = items")]
    [InlineData("first, middle......, last = 1, 2, 3")]
    public void MalformedCollectingForms_DoNotCreateRecoveredCollectingBindings(string source)
    {
        var syntax = Parser.ParseSyntax(source);
        var parse = Parser.Parse(source);

        Assert.True(syntax.HasErrors);
        Assert.True(parse.HasErrors);
        AssertNoVariadicBindings(syntax.Root);
        AssertNoVariadicBindings(parse.Root);
    }

    [Fact]
    public void CombinedPrefixAndPostfixMarkers_InParameterPattern_ReportOneMalformedError()
    {
        var parse = Parser.Parse("F(first, ...middle..., last) = middle");

        var error = Assert.Single(parse.Diagnostics);
        Assert.Equal(DiagnosticSeverity.Error, error.Severity);
        Assert.Equal(
            "Malformed collecting binding; write `middle...` with exactly one postfix `...` marker.",
            error.Message);
        AssertNoVariadicBindings(parse.Root);
    }

    [Theory]
    [InlineData(
        "Broken(...items) = items\nGood(values...) = values\nGood(1, 2)")]
    [InlineData(
        "first, ...middle, last = values\nGood(values...) = values\nGood(1, 2)")]
    public void PrefixBindingSpelling_RecoversSoFollowingDeclarationsStillParse(string source)
    {
        var parse = Parser.Parse(source);

        Assert.True(parse.HasErrors);
        var good = Assert.Single(parse.Root.Properties, property => property.Name == "Good").Value;
        var parameter = Assert.Single(good.Parameters);
        Assert.Equal(ParameterKind.Variadic, parameter.Kind);
        Assert.Equal("values...", parameter.DisplayName);
    }

    [Fact]
    public void PostfixCollectingBinding_MarkerAllowsSameLineWhitespaceButNotANewline()
    {
        // Same-line whitespace between the binding name and its marker stays a
        // collecting binding; a marker on the NEXT line never continues it.
        Assert.Equal("[1, 2]", Display("F(items ...) = items\nF(1, 2)"));
        Assert.True(Parser.Parse("F(items\n...) = items\nF(1)").HasErrors);
    }

    [Fact]
    public void PostfixCollectingBinding_DotReceiverRemainsOneSlotUnlessExplicitlySpread()
    {
        Assert.Equal("[[1, 2]]", Display("F(items...) = items\nA = [1, 2]\nA.F"));
        Assert.Equal("[1, 2]", Display("F(items...) = items\nA = [1, 2]\n(spread(A)).F"));
    }

    private sealed class CollectingBindingFinder : AstWalker
    {
        public List<string> VariadicBindings { get; } = [];

        protected override void VisitExplicitParameterDeclaration(
            Algorithm algorithm,
            ParameterDeclaration declaration)
        {
            if (declaration.Kind == ParameterKind.Variadic)
                VariadicBindings.Add(declaration.Name);
        }

        protected override void VisitConditionalBinderDeclaration(Pattern.Bind pattern, SourceSpan span)
        {
            if (pattern.ParameterKind == ParameterKind.Variadic)
                VariadicBindings.Add(pattern.Name);
        }
    }

    private static void AssertNoVariadicBindings(Algorithm root)
    {
        var collectingFinder = new CollectingBindingFinder();
        collectingFinder.VisitAlgorithm(root);
        Assert.Empty(collectingFinder.VariadicBindings);
    }
}
