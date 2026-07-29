namespace KatLang.Tests;

/// <summary>
/// Surface-syntax rules for collecting bindings. Prefix <c>*name</c> —
/// the collect marker directly attached to its binding name — is the ONLY
/// collecting-binding spelling, valid only in binding positions: explicit
/// parameter lists, nested sequence-value parameter patterns, and
/// assignment deconstruction targets. The marker requires exact
/// source-offset attachment (no whitespace, comment, or newline between the
/// star and the name), and exactly one marker forms a binding. Malformed
/// shapes report targeted diagnostics and never create a collecting binding
/// in the recovered tree.
/// </summary>
public class CollectingBindingSyntaxTests
{
    private static string Display(string source)
    {
        var result = KatLangEngine.Run(source);
        Assert.True(result is RunResult.Success, $"Expected success but got: {result.ToDisplayString()}");
        return result.ToDisplayString().Replace("\r\n", "\n");
    }

    private static ParseResult Parse(string source) => Parser.Parse(source);

    // ── Canonical orientation and spans ─────────────────────────────────────

    [Fact]
    public void PrefixCollectingBinding_ParsesCanonicalOrientationWithExactSpans()
    {
        var parse = Parse("Collect(*items) = items\nCollect(1, 2)");
        Assert.Empty(parse.Diagnostics);

        var collect = Assert.Single(parse.Root.Properties, static p => p.Name == "Collect");
        var parameter = Assert.Single(collect.Value.ExplicitParameters);
        Assert.Equal(ParameterKind.Collecting, parameter.Kind);
        Assert.Equal(new SourceSpan(1, 9, 1, 9), parameter.CollectMarkerSpan);
        Assert.Equal(new SourceSpan(1, 10, 1, 14), parameter.Span);
        Assert.Equal("*items", parameter.DisplayName);
    }

    [Fact]
    public void MixedParameterList_MarkerSitsOnTheMiddleBinding()
    {
        var parse = Parse("Middle(first, *middle, last) = middle\nMiddle(1, 2, 3)");
        Assert.Empty(parse.Diagnostics);

        var middle = Assert.Single(parse.Root.Properties, static p => p.Name == "Middle");
        var parameters = middle.Value.ExplicitParameters;
        Assert.Equal(3, parameters.Count);
        Assert.Equal(ParameterKind.Normal, parameters[0].Kind);
        Assert.Equal(ParameterKind.Collecting, parameters[1].Kind);
        Assert.Equal(ParameterKind.Normal, parameters[2].Kind);
        Assert.Equal(new SourceSpan(1, 15, 1, 15), parameters[1].CollectMarkerSpan);
    }

    [Fact]
    public void NestedSequenceValuePattern_SupportsThePrefixMarker()
    {
        var parse = Parse("F((head, *tail)) = tail\nF((1, 2, 3))");
        Assert.Empty(parse.Diagnostics);
        Assert.Equal("[2, 3]", Display("F((head, *tail)) = tail\nF((1, 2, 3))"));
    }

    [Fact]
    public void DeconstructionTargets_SupportThePrefixMarkerInEveryPosition()
    {
        Assert.Equal("[1, 2, 3]", Display("*all = 1, 2, 3\nall"));
        Assert.Equal("[2]", Display("a, *mid, z = 1, 2, 3\nmid"));
        Assert.Equal("[1, 2]", Display("*init, z = 1, 2, 3\ninit"));
        Assert.Equal("[2, 3]", Display("a, *rest = 1, 2, 3\nrest"));
    }

    // ── Attachment: no whitespace, comment, or newline ──────────────────────

    [Theory]
    [InlineData("F(* items) = items\nF(1)")]
    [InlineData("F(a, * mid, z) = mid\nF(1, 2, 3)")]
    public void DetachedMarker_InParameterList_ReportsAttachmentDiagnostic(string source)
    {
        var parse = Parse(source);
        Assert.True(parse.HasErrors);
        var error = Assert.Single(parse.Diagnostics);
        Assert.Contains("must be directly attached to its binding name", error.Message);
    }

    [Fact]
    public void DetachedMarker_ReportsExactSourceSpan()
    {
        var parse = Parse("F(* items) = items\nF(1)");
        var error = Assert.Single(parse.Diagnostics);
        // Span covers the star through the detached name: columns 3..9.
        Assert.Equal(new SourceSpan(1, 3, 1, 9), error.Span);
    }

    [Fact]
    public void MarkerSeparatedByNewline_IsAnAttachmentError()
    {
        var parse = Parse("F(*\nitems) = items\nF(1)");
        Assert.True(parse.HasErrors);
        Assert.Contains(parse.Diagnostics, static d => d.Message.Contains("directly attached")
            || d.Message.Contains("followed by a binding name"));
    }

    [Fact]
    public void DetachedMarker_RecoversWithAFixedBinding_NeverCollecting()
    {
        var parse = Parse("F(* items) = items\nF(1)");
        var f = Assert.Single(parse.Root.Properties, static p => p.Name == "F");
        var parameter = Assert.Single(f.Value.ExplicitParameters);
        Assert.Equal(ParameterKind.Normal, parameter.Kind);
        Assert.Null(parameter.CollectMarkerSpan);
        AssertNoCollectingBindings(parse.Root);
    }

    // ── Exactly one marker ──────────────────────────────────────────────────

    [Theory]
    [InlineData("F(**items) = items\nF(1)")]
    [InlineData("F(***items) = items\nF(1)")]
    public void RepeatedMarker_InParameterList_ReportsOneDiagnostic_NoCollectingBinding(string source)
    {
        var parse = Parse(source);
        var error = Assert.Single(parse.Diagnostics);
        Assert.Contains("exactly one collect marker", error.Message);
        AssertNoCollectingBindings(parse.Root);
    }

    [Fact]
    public void RepeatedMarker_InDeconstruction_ReportsOneDiagnostic_NoCollectingBinding()
    {
        var parse = Parse("a, **mid, z = 1, 2, 3\na");
        Assert.Contains(parse.Diagnostics, static d => d.Message.Contains("exactly one collect marker"));
        AssertNoCollectingBindings(parse.Root);
    }

    [Fact]
    public void TwoCollectingBindings_PerPatternLevel_AreRejected()
    {
        var parse = Parse("F(*a, *b) = a\nF(1, 2)");
        Assert.Contains(parse.Diagnostics, static d => d.Message.Contains("Only one collecting binding is allowed per pattern level."));
    }

    [Fact]
    public void TwoCollectingTargets_InDeconstruction_AreRejected()
    {
        var parse = Parse("*a, *b = 1, 2, 3\na");
        Assert.Contains(parse.Diagnostics, static d =>
            d.Message.Contains("at most one collecting binding (`*name`)"));
    }

    // ── Marker without a name ───────────────────────────────────────────────

    [Theory]
    [InlineData("F(*) = 0")]
    [InlineData("F(*, x) = x")]
    [InlineData("F(*1) = 0")]
    public void MarkerWithoutABindingName_ReportsMissingNameDiagnostic(string source)
    {
        var parse = Parse(source);
        Assert.True(parse.HasErrors);
        Assert.Contains(parse.Diagnostics, static d =>
            d.Message.Contains("must be followed by a binding name"));
        AssertNoCollectingBindings(parse.Root);
    }

    // ── Postfix star is never binding syntax ────────────────────────────────

    [Theory]
    [InlineData("F(items*) = items\nF(1)")]
    [InlineData("F(a, rest*) = rest\nF(1, 2)")]
    public void PostfixStar_InBindingPattern_ReportsSpreadMarkerDiagnostic(string source)
    {
        var parse = Parse(source);
        Assert.True(parse.HasErrors);
        Assert.Contains(parse.Diagnostics, static d =>
            d.Message.Contains("Postfix `*` is the spread marker and is not valid in a binding pattern"));
        AssertNoCollectingBindings(parse.Root);
    }

    // ── Prefix star outside binding positions ───────────────────────────────

    [Theory]
    [InlineData("x = *values\nvalues = 1, 2\nx")]
    [InlineData("A = (1, 2)\nF(x) = x\nF(*A)")]
    [InlineData("A = (1, 2)\n[*A]")]
    public void PrefixStar_InExpressionPosition_ReportsCollectMarkerDiagnostic(string source)
    {
        var parse = Parse(source);
        Assert.True(parse.HasErrors);
        Assert.Contains(parse.Diagnostics, static d =>
            d.Message.Contains("Prefix `*` is the collect marker and is valid only in binding patterns"));
    }

    [Fact]
    public void PrefixStar_InExpressionPosition_RecoversToTheOperand()
    {
        // `x = *values` degrades to `x = values` after the targeted error.
        var parse = Parse("values = (1, 2)\nx = *values\nx");
        Assert.True(parse.HasErrors);
        var x = Assert.Single(parse.Root.Properties, static p => p.Name == "x");
        Assert.IsType<Expr.Resolve>(Assert.Single(x.Value.Output));
    }

    // ── Grace interactions ──────────────────────────────────────────────────

    [Fact]
    public void GraceAfterTheCollectingName_ReportsGraceError_KeepsTheCollectingBinding()
    {
        var parse = Parse("F(*items~) = items\nF(1)");
        Assert.Contains(parse.Diagnostics, static d => d.Message.Contains("Collecting bindings cannot use `~` reordering."));

        var f = Assert.Single(parse.Root.Properties, static p => p.Name == "F");
        var parameter = Assert.Single(f.Value.ExplicitParameters);
        Assert.Equal(ParameterKind.Collecting, parameter.Kind);
    }

    [Fact]
    public void GraceBeforeTheMarker_ReportsGraceError_KeepsTheCollectingBinding()
    {
        var parse = Parse("F(~*items) = items\nF(1)");
        Assert.Contains(parse.Diagnostics, static d => d.Message.Contains("Grace is not allowed in clause-head patterns."));

        var f = Assert.Single(parse.Root.Properties, static p => p.Name == "F");
        var parameter = Assert.Single(f.Value.ExplicitParameters);
        Assert.Equal(ParameterKind.Collecting, parameter.Kind);
    }

    // ── Recovery keeps later declarations intact ────────────────────────────

    [Theory]
    [InlineData("F(* items) = items\nG = 5\nG")]
    [InlineData("F(**items) = items\nG = 5\nG")]
    [InlineData("F(items*) = items\nG = 5\nG")]
    public void MalformedMarkerForms_LaterDeclarationsStillParse(string source)
    {
        var parse = Parse(source);
        Assert.True(parse.HasErrors);
        Assert.Contains(parse.Root.Properties, static p => p.Name == "G");
    }

    // ── Old ellipsis spellings fail through ordinary parsing ────────────────

    [Theory]
    [InlineData("F(items...) = items\nF(1)")]
    [InlineData("F(...items) = items\nF(1)")]
    [InlineData("items... = 1, 2\nitems")]
    [InlineData("...items = 1, 2\nitems")]
    [InlineData("x, y..., z = 1, 2, 3\ny")]
    [InlineData("F((a, b...)) = b\nF((1, 2))")]
    public void OldEllipsisSpellings_FailThroughOrdinaryParsing_NoCollectingBinding(string source)
    {
        var parse = Parse(source);
        Assert.True(parse.HasErrors, $"expected errors for: {source}");
        // No ellipsis-specific diagnostic exists anymore: the dots fail as
        // ordinary unexpected/dot-member tokens.
        Assert.DoesNotContain(parse.Diagnostics, static d => d.Message.Contains("..."));
        AssertNoCollectingBindings(parse.Root);
    }

    // ── Helper: assert the recovered tree contains no collecting binding ────

    private static void AssertNoCollectingBindings(Algorithm root)
    {
        var detector = new CollectingBindingDetector();
        detector.VisitAlgorithm(root);
        Assert.False(detector.Found, "recovered tree must not contain a collecting binding");
    }

    private sealed class CollectingBindingDetector : AstWalker
    {
        public bool Found { get; private set; }

        protected override void VisitExplicitParameterDeclaration(Algorithm algorithm, ParameterDeclaration parameter)
        {
            if (parameter.Kind == ParameterKind.Collecting)
                Found = true;
        }
    }
}
