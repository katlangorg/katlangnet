using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// Editor-facing alias surface, derived entirely from the semantic prelude:
/// catalog completion entries, hover signatures, builtin classification, the
/// absence of source declaration spans, ordinary shadowing in visible-symbol
/// enumeration, dot-call eligibility, and the canonical-only Math member list.
/// </summary>
public class MathAliasSemanticModelTests
{
    private static SemanticModel BuildModel(string source)
    {
        var parseResult = Parser.Parse(source);
        Assert.False(
            parseResult.HasErrors,
            string.Join(Environment.NewLine, parseResult.Diagnostics.Select(d => d.Message)));
        return SemanticModelBuilder.Build(parseResult);
    }

    private static IdentifierResolution ResolutionAt(SemanticModel model, int line, int column)
        => Assert.IsType<IdentifierResolution>(model.FindResolutionAt(line, column));

    private static VisibleSymbol CatalogSymbol(string name)
        => Assert.Single(PreludeCatalog.Symbols, symbol => symbol.Name == name);

    [Fact]
    public void PreludeCatalog_ContainsEveryAliasAsBuiltinWithoutDeclaration()
    {
        foreach (var alias in BuiltinRegistry.MathAliasNames)
        {
            var symbol = CatalogSymbol(alias);
            Assert.Equal(IdentifierClassification.Builtin, symbol.Classification);
            Assert.Null(symbol.Declaration);

            var property = symbol.Property!;
            Assert.Equal(PropertyShape.Builtin, property.Shape);
            Assert.Null(property.Declaration);

            // An alias exposes no structural member surface of its own.
            Assert.Empty(symbol.Members);
        }
    }

    [Fact]
    public void PreludeCatalog_AliasSignaturesUseDescriptorParameterNames()
    {
        Assert.Equal("round(x, y)", CatalogSymbol("round").Property!.GetDisplaySignature(PropertyCallStyle.Plain));
        Assert.Equal("atan2(y, x)", CatalogSymbol("atan2").Property!.GetDisplaySignature(PropertyCallStyle.Plain));
        Assert.Equal("random(start, end)", CatalogSymbol("random").Property!.GetDisplaySignature(PropertyCallStyle.Plain));
        Assert.Equal("randomInt(start, end)", CatalogSymbol("randomInt").Property!.GetDisplaySignature(PropertyCallStyle.Plain));
        Assert.Equal("sqrt(x)", CatalogSymbol("sqrt").Property!.GetDisplaySignature(PropertyCallStyle.Plain));
        Assert.Equal("exp(x)", CatalogSymbol("exp").Property!.GetDisplaySignature(PropertyCallStyle.Plain));
        Assert.Equal("pow(x, y)", CatalogSymbol("pow").Property!.GetDisplaySignature(PropertyCallStyle.Plain));

        // Constants are zero-parameter property-like entries.
        Assert.Empty(CatalogSymbol("pi").Property!.Parameters);
        Assert.Empty(CatalogSymbol("pi").Property!.Signatures);

        // The REPLACED Euler constant left no catalog residue: no lowercase
        // `e` binding and no canonical `E` member survive anywhere.
        Assert.DoesNotContain(PreludeCatalog.Symbols, symbol => symbol.Name == "e");
        var math = CatalogSymbol("Math");
        Assert.DoesNotContain(math.Members, member => member.Name == "E");
        Assert.Equal(
            "Exp(x)",
            Assert.Single(math.Members, member => member.Name == "Exp")
                .Property!.GetDisplaySignature(PropertyCallStyle.Plain));
    }

    [Fact]
    public void PreludeCatalog_AliasDotCallEligibilityAgreesWithRuntime()
    {
        // `v.cos` genuinely runs as `cos(v)` at runtime, so the editor offers
        // the dot surface; the receiver consumes the first parameter.
        var cos = CatalogSymbol("cos").Property!;
        Assert.True(cos.SupportsLexicalDotCall);
        Assert.Equal("x.cos", cos.FindSignature(PropertyCallStyle.Dot)!.DisplayText);

        var atan2 = CatalogSymbol("atan2").Property!;
        Assert.Equal("y.atan2(x)", atan2.FindSignature(PropertyCallStyle.Dot)!.DisplayText);

        var exp = CatalogSymbol("exp").Property!;
        Assert.Equal("x.exp", exp.FindSignature(PropertyCallStyle.Dot)!.DisplayText);

        // `load` remains the front-end-only contrast case.
        Assert.False(CatalogSymbol("load").Property!.SupportsLexicalDotCall);
    }

    [Fact]
    public void PreludeCatalog_MathMemberListStaysCanonicalPascalCase()
    {
        var math = CatalogSymbol("Math");
        Assert.Equal(
            BuiltinRegistry.MathMemberNames.OrderBy(static name => name, StringComparer.Ordinal),
            math.Members.Select(static member => member.Name).OrderBy(static name => name, StringComparer.Ordinal));

        foreach (var alias in BuiltinRegistry.MathAliasNames)
            Assert.DoesNotContain(math.Members, member => member.Name == alias);
    }

    [Fact]
    public void AliasReference_ClassifiesAsBuiltinWithoutDeclarationTarget()
    {
        var model = BuildModel("cos(1)");

        var resolution = ResolutionAt(model, 1, 1);
        Assert.Equal(OccurrenceKind.ResolveReference, resolution.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.Builtin, resolution.Classification);
        Assert.Null(resolution.ResolvedDeclaration);

        // Hover metadata carries the descriptor signature; go-to-definition has
        // no source target because the alias is synthetic.
        var property = Assert.IsType<PropertyInfo>(model.FindPropertyAt(1, 1));
        Assert.Equal(PropertyShape.Builtin, property.Shape);
        Assert.Equal("cos(x)", property.DisplaySignature);
        Assert.Null(property.Declaration);
    }

    [Fact]
    public void UnshadowedScope_OffersAliasesInVisibleSymbols()
    {
        var model = BuildModel("Value = 1\nValue");
        var visible = model.GetVisibleSymbolsAt(2, 1);

        foreach (var alias in BuiltinRegistry.MathAliasNames)
        {
            var symbol = Assert.Single(visible, candidate => candidate.Name == alias);
            Assert.Equal(IdentifierClassification.Builtin, symbol.Classification);
            Assert.Null(symbol.Declaration);
        }
    }

    [Fact]
    public void LocalDeclaration_ShadowsAliasInVisibleSymbolsAndResolution()
    {
        var model = BuildModel("sin(x) = x * 10\nsin(3)");

        // Completion offers exactly ONE `sin`: the local property, with its
        // declaration site, not the builtin alias.
        var visible = model.GetVisibleSymbolsAt(2, 1);
        var symbol = Assert.Single(visible, candidate => candidate.Name == "sin");
        Assert.Equal(IdentifierClassification.PropertyReference, symbol.Classification);
        Assert.NotNull(symbol.Declaration);

        // And the reference resolves to that declaration.
        var resolution = ResolutionAt(model, 2, 1);
        Assert.Equal(IdentifierClassification.PropertyReference, resolution.Classification);
        Assert.Equal(Assert.Single(model.FindDeclarations("sin")), resolution.ResolvedDeclaration);
    }

    [Fact]
    public void ExplicitParameterPi_ShadowsAliasInResolution()
    {
        var model = BuildModel("F(pi) = pi + 1\nF(5)");

        var resolution = ResolutionAt(model, 1, 9);
        Assert.Equal(OccurrenceKind.ParameterReference, resolution.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.ExplicitParameterReference, resolution.Classification);
        Assert.NotNull(resolution.ResolvedDeclaration);
    }

    [Fact]
    public void MathLowercaseMemberOccurrence_NeverResolvesToACanonicalMember()
    {
        // `Math.cos` is not a Math member: the member occurrence resolves only
        // through the ordinary lexical fallback (the alias builtin), with no
        // canonical declaration target — mirroring the runtime, which rejects
        // `Math.cos(1)` instead of computing.
        var model = BuildModel("Math.cos");
        var resolution = ResolutionAt(model, 1, 6);
        Assert.Equal(OccurrenceKind.DotMemberReference, resolution.Occurrence.Kind);
        Assert.Equal(IdentifierClassification.Builtin, resolution.Classification);
        Assert.Null(resolution.ResolvedDeclaration);
    }

    [Fact]
    public void LocallyShadowedMathMember_ResolvesToTheUserDeclaration()
    {
        var model = BuildModel("Math = { public cos(x) = x }\nMath.cos(1)");
        var resolution = ResolutionAt(model, 2, 6);

        Assert.Equal(IdentifierClassification.PropertyReference, resolution.Classification);
        Assert.Equal(Assert.Single(model.FindDeclarations("cos")), resolution.ResolvedDeclaration);
    }
}
