namespace KatLang.Tests;

public class CollectingBindingSyntaxTests
{
    private static string Display(string source)
    {
        var result = KatLangEngine.Run(source);
        Assert.True(result is RunResult.Success, $"Expected success but got: {result.ToDisplayString()}");
        return result.ToDisplayString();
    }

    [Fact]
    public void PrefixCollectingBinding_CollectsEmptySingletonAndMultipleArgumentsAsExactLists()
    {
        Assert.Equal("[]", Display("F(...items) = items\nF()"));
        Assert.Equal("[1]", Display("F(...items) = items\nF(1)"));
        Assert.Equal("[1, 2, 3]", Display("F(...items) = items\nF(1, 2, 3)"));
    }

    [Fact]
    public void PrefixCollectingBinding_SupportsSumAndMovableMiddle()
    {
        Assert.Equal("6", Display("Sum(...items) = items.sum\nSum(1, 2, 3)"));
        Assert.Equal(
            "[2, 3, 4]",
            Display("Middle(first, ...middle, last) = middle\nMiddle(1, 2, 3, 4, 5)"));
    }

    [Fact]
    public void PrefixCollectingBinding_SupportsFrontMiddleAndFinalPositions()
    {
        Assert.Equal("[1, 2]", Display("F(...prefix, last) = prefix\nF(1, 2, 3)"));
        Assert.Equal("[2, 3]", Display("F(first, ...middle, last) = middle\nF(1, 2, 3, 4)"));
        Assert.Equal("[2, 3]", Display("F(first, ...suffix) = suffix\nF(1, 2, 3)"));
    }

    [Fact]
    public void PrefixCollectingDeconstruction_CollectsMovableMiddleAsExactList()
        => Assert.Equal(
            "(1, [2, 3, 4], 5)",
            Display(
                """
                first, ...middle, last = 1, 2, 3, 4, 5
                (first, middle, last)
                """));

    [Fact]
    public void Forwarding_UsesPrefixCollectAndPostfixOpenAsOppositeOperations()
        => Assert.Equal(
            "[1, 2, 3]",
            Display(
                """
                Target(...items) = items
                Forward(...items) = Target(items...)
                Forward(1, 2, 3)
                """));

    [Theory]
    [InlineData("F([1, 2])", "[[1, 2]]")]
    [InlineData("F([1, 2]...)", "[1, 2]")]
    [InlineData("F((1, 2))", "[(1, 2)]")]
    [InlineData("F((1, 2)...)", "[1, 2]")]
    [InlineData("F([])", "[[]]")]
    [InlineData("F([]...)", "[]")]
    [InlineData("F(())", "[()]")]
    [InlineData("F(()...)", "[]")]
    public void PrefixCollectingBinding_PreservesExistingListAndSequenceArgumentBoundaries(
        string call,
        string expected)
        => Assert.Equal(expected, Display($"F(...items) = items\n{call}"));

    /// <summary>
    /// The central orientation test: ONE source containing both ellipsis forms, proving
    /// the left occurrence elaborates to a collecting binding and the right to a spread
    /// expression, and that neither is mistaken for the other.
    /// </summary>
    [Fact]
    public void PrefixIsACollectingBindingAndPostfixIsASpread_InTheSameDeclaration()
    {
        const string source =
            """
            Target(...items) = items
            Forward(...items) = Target(items...)
            Forward(1, 2, 3)
            """;

        var parse = Parser.Parse(source);
        Assert.Empty(parse.Diagnostics);

        var forward = Assert.Single(parse.Root.Properties, property => property.Name == "Forward").Value;

        // Left `...items`: a collecting binding carrying the source-backed marker span.
        var parameter = Assert.Single(forward.Parameters);
        Assert.Equal(ParameterKind.Variadic, parameter.Kind);
        Assert.Equal("...items", parameter.DisplayName);
        Assert.Equal(new SourceSpan(2, 9, 2, 11), parameter.CollectingMarkerSpan);

        // Right `items...`: a spread expression over the bound variadic parameter, not a binding.
        var call = Assert.IsType<Expr.Call>(Assert.Single(forward.Output));
        var spread = Assert.IsType<Expr.SequenceSpread>(Assert.Single(call.Args.Output));
        Assert.Equal("items", Assert.IsType<Expr.Param>(spread.Operand).Name);

        Assert.Equal("[1, 2, 3]", Display(source));
    }

    [Theory]
    [InlineData("F(items...) = items", "items", 3, 10)]
    [InlineData("F(first, middle..., last) = middle", "middle", 10, 18)]
    [InlineData("F(items..., last) = items", "items", 3, 10)]
    [InlineData("F(first, items...) = items", "items", 10, 17)]
    [InlineData("items... = values", "items", 1, 8)]
    [InlineData("first, middle..., last = values", "middle", 8, 16)]
    [InlineData("items..., last = values", "items", 1, 8)]
    [InlineData("first, items... = values", "items", 8, 15)]
    public void PostfixBindingSpelling_IsRejectedEverywhere(
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
            "Postfix `...` is the spread operator and cannot declare a collecting binding. "
                + $"Write `...{name}` instead of `{name}...`.",
            error.Message);
        Assert.Equal(new SourceSpan(1, startColumn, 1, endColumn), error.Span);

        // A clean break: nothing is accepted with a warning.
        Assert.DoesNotContain(parse.Diagnostics, static diagnostic =>
            diagnostic.Severity == DiagnosticSeverity.Warning);

        AssertNoVariadicBindings(syntax.Root);
        AssertNoVariadicBindings(parse.Root);
    }

    [Theory]
    [InlineData("F(...items) = items\nA = 1, 2\nF(A...)")]
    [InlineData("F(...items) = items\nF([1, 2]...)")]
    [InlineData("F(...items) = items\nF((1, 2)...)")]
    [InlineData("Values = 1, 2, 3\nfirst, ...middle, last = Values...\nmiddle")]
    public void PostfixSpread_RemainsValidAndUnaffected(string source)
        => Assert.Empty(Parser.Parse(source).Diagnostics);

    [Theory]
    [InlineData("F(...a, ...b) = a", "Only one collecting binding")]
    [InlineData("...a, ...b = 1, 2", "at most one collecting binding")]
    [InlineData("F(...items...) = items", "Malformed collecting binding")]
    [InlineData("first, ...middle..., last = 1, 2, 3", "Malformed collecting binding")]
    [InlineData("F(...a, b...) = a", "cannot declare a collecting binding")]
    [InlineData("F(a..., ...b) = b", "cannot declare a collecting binding")]
    public void MalformedCollectingForms_FailSafelyWithATargetedDiagnostic(
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
    [InlineData("first, ...middle..., last = 1, 2, 3")]
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
    public void CombinedPrefixAndPostfixMarkers_ReportsOneTargetedError()
    {
        var parse = Parser.Parse("first, ...middle..., last = values");

        var error = Assert.Single(parse.Diagnostics);
        Assert.Equal(DiagnosticSeverity.Error, error.Severity);
        Assert.Equal(
            "Malformed collecting binding `...middle...`; write `...middle`. "
                + "Postfix `...` is reserved for value spreading.",
            error.Message);
        Assert.Equal(new SourceSpan(1, 8, 1, 19), error.Span);
    }

    [Theory]
    [InlineData(
        "Broken(items...) = items\nGood(...values) = values\nGood(1, 2)")]
    [InlineData(
        "first, middle..., last = values\nGood(...values) = values\nGood(1, 2)")]
    public void PostfixBindingSpelling_RecoversSoFollowingDeclarationsStillParse(string source)
    {
        var parse = Parser.Parse(source);

        Assert.True(parse.HasErrors);
        var good = Assert.Single(parse.Root.Properties, property => property.Name == "Good").Value;
        var parameter = Assert.Single(good.Parameters);
        Assert.Equal(ParameterKind.Variadic, parameter.Kind);
        Assert.Equal("...values", parameter.DisplayName);
    }

    [Fact]
    public void PrefixCollectingBinding_DotReceiverRemainsOneSlotUnlessExplicitlySpread()
    {
        Assert.Equal("[[1, 2]]", Display("F(...items) = items\nA = [1, 2]\nA.F"));
        Assert.Equal("[1, 2]", Display("F(...items) = items\nA = [1, 2]\n(A...).F"));
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
