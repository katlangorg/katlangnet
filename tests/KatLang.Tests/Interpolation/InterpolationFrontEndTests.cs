using KatLang.Semantics;

namespace KatLang.Tests.Interpolation;

/// <summary>
/// STR-02 front end: a hole is ONE ordinary expression of the ENCLOSING owner — never a scope —
/// so every front-end rule reads it exactly as it reads an operand: name resolution and
/// ownership, implicit-parameter inference in first-occurrence order, Grace, the VALUE role of
/// the unified formula-lifting law, closed-list checks, and the editor's semantic model (sites,
/// hover/definition, references, visible symbols) inside holes.
/// </summary>
public class InterpolationFrontEndTests
{
    private static string Display(string source)
        => Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString().ReplaceLineEndings("\n");

    private static IReadOnlyList<string> ParameterNames(string source, string property)
    {
        var root = SourceProvenance.ParseValid(source).Root;
        var algorithm = Assert.IsType<Algorithm.User>(Assert.Single(root.Properties, p => p.Name == property).Value);
        return algorithm.Parameters.Select(p => p.Name).ToList();
    }

    [Fact]
    public void FreeNamesInHoles_AreInferredInFirstOccurrenceOrder()
    {
        Assert.Equal(new[] { "b", "a" }, ParameterNames("F = \"{b}-{a}-{b}\"\nF(1, 2)", "F"));
        Assert.Equal("1-2-1", Display("F = \"{b}-{a}-{b}\"\nF(1, 2)"));
    }

    [Fact]
    public void Grace_ReordersInferredParameters_InsideHoles()
    {
        Assert.Equal(new[] { "a", "b" }, ParameterNames("F = \"{b}-{~a}\"\nF(1, 2)", "F"));
        Assert.Equal("2-1", Display("F = \"{b}-{~a}\"\nF(1, 2)"));
    }

    [Fact]
    public void AHoleIsAValueRole_SoACallableThatRequiresArgumentsIsLifted()
    {
        Assert.Equal(new[] { "x" }, ParameterNames("Inc(x) = x + 1\nG = \"<{Inc}>\"\nG(4)", "G"));
        Assert.Equal("<5>", Display("Inc(x) = x + 1\nG = \"<{Inc}>\"\nG(4)"));
    }

    [Fact]
    public void AZeroArgumentCallableInAHole_IsReadNotLifted()
    {
        Assert.Empty(ParameterNames("Only(*xs) = xs\nG = \"{Only}\"\nG", "G"));
        Assert.Equal("[]", Display("Only(*xs) = xs\nG = \"{Only}\"\nG"));
    }

    [Fact]
    public void Ownership_AParameterBeatsAPropertyOfAFartherOwner()
        => Assert.Equal("2\n1", Display("v = 1\nF(v) = \"{v}\"\nF(2), \"{v}\""));

    [Fact]
    public void AHoleIsNotAScope_NamesResolveInTheEnclosingAlgorithm()
        => Assert.Equal("6", Display("F(x) = { y = x * 2\n \"{y + x - x}\" }\nF(3)"));

    [Fact]
    public void AClosedListBody_ChecksTheNamesOfItsHoles()
    {
        var diagnostics = SourceProvenance.ExpectFrontEndError("G(y) = \"{z}\"\nG(1)");
        Assert.Contains(diagnostics, d => d.Code == DiagnosticCode.UndeclaredIdentifier);
    }

    [Fact]
    public void AnUnresolvedRootName_InAHole_IsTheRootsImplicitParameterError()
    {
        var error = SourceProvenance.ParseValid("\"{nope}\"").ExpectEvaluationError<EvalError.UnresolvedImplicitParams>();
        Assert.Equal(new[] { "nope" }, error.ParamNames);
    }

    [Fact]
    public void BareForwarding_AndFormulaLifting_SeeHolesLikeOperands()
    {
        Assert.Equal("10 is ten", Display("Say(n, w) = \"{n} is {w}\"\nT(n, w) = Say\nT(10, 'ten')"));
        Assert.Equal("(4!)", Display("Shout(x) = \"{x}!\"\nWrap = \"({Shout})\"\nWrap(4)"));
    }

    [Fact]
    public void DotCallsInHoles_FollowTheOrdinaryDotRoute()
        => Assert.Equal("2|3|[1]", Display("Obj = { public V = 3 }\n\"{(1, 2).count}|{Obj.V}|{[1, 2].take(1)}\""));

    // ── Semantic model ─────────────────────────────────────────────────────

    [Fact]
    public void ANameInAHole_ResolvesToItsDeclaration_ForHoverAndDefinition()
    {
        var parsed = SourceProvenance.ParseValid("value = 5\n\"a{value}b\"");
        var model = SemanticModelBuilder.Build(parsed.Parsed);
        var resolution = Assert.IsType<IdentifierResolution>(model.FindResolutionAt(new SourcePosition(2, 5)));
        Assert.Equal("value", resolution.Occurrence.Name);
        Assert.Equal(new SourceSpan(2, 4, 2, 9), resolution.Occurrence.Span);
        Assert.Equal(IdentifierClassification.PropertyReference, resolution.Classification);
        Assert.NotNull(resolution.ResolvedDeclaration);
        Assert.Equal(new SourcePosition(1, 1), resolution.ResolvedDeclaration.Span.Start);
    }

    [Fact]
    public void ReferencesInHoles_AreFoundWithEveryOtherReference()
    {
        var parsed = SourceProvenance.ParseValid("k = 1\n\"{k}{k}\", k + k");
        var model = SemanticModelBuilder.Build(parsed.Parsed);
        var references = model.FindResolutions("k").Where(r => r.Classification == IdentifierClassification.PropertyReference).ToList();
        Assert.Equal(4, references.Count);
        Assert.All(references, r => Assert.Equal(2, r.Occurrence.Span.Start.Line));
    }

    [Fact]
    public void AnImplicitParameterInAHole_IsClassifiedAsOne()
    {
        var parsed = SourceProvenance.ParseValid("F = \"{p}\"\nF(1)");
        var model = SemanticModelBuilder.Build(parsed.Parsed);
        var resolution = Assert.IsType<IdentifierResolution>(model.FindResolutionAt(new SourcePosition(1, 7)));
        Assert.Equal("p", resolution.Occurrence.Name);
        Assert.Equal(IdentifierClassification.ImplicitParameterReference, resolution.Classification);
    }

    [Fact]
    public void TheSymbolsVisibleInAHole_AreTheEnclosingAlgorithmsSymbols()
    {
        var parsed = SourceProvenance.ParseValid("Outer(x) = { inner = 2\n\"{x + inner}\" }\nOuter(1)");
        var model = SemanticModelBuilder.Build(parsed.Parsed);
        var visible = model.GetVisibleSymbolsAt(new SourcePosition(2, 4)).Select(s => s.Name).ToList();
        Assert.Contains("x", visible);
        Assert.Contains("inner", visible);
        Assert.Contains("Outer", visible);
    }

    [Fact]
    public void TextAndBraces_ProduceNoSites()
    {
        var parsed = SourceProvenance.ParseValid("\"name {1} {{x}}\"");
        var model = SemanticModelBuilder.Build(parsed.Parsed);
        Assert.Empty(model.IdentifierOccurrences);
        Assert.Null(model.FindResolutionAt(new SourcePosition(1, 3)));
    }

    [Fact]
    public void AMalformedHole_StillModelsTheValidHoles()
    {
        var parsed = SourceProvenance.ParseAllowingDiagnostics("good = 1\n\"{good}{,}\"");
        Assert.Contains(parsed.Diagnostics, d => d.Code == DiagnosticCode.InvalidInterpolationHole);
        var model = SemanticModelBuilder.Build(parsed.Parsed);
        var resolution = Assert.IsType<IdentifierResolution>(model.FindResolutionAt(new SourcePosition(2, 3)));
        Assert.Equal("good", resolution.Occurrence.Name);
    }
}
