using System.Text.Json;
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
        Assert.Equal("round(value, digits)", CatalogSymbol("round").Property!.GetDisplaySignature(PropertyCallStyle.Plain));
        Assert.Equal("atan2(y, x)", CatalogSymbol("atan2").Property!.GetDisplaySignature(PropertyCallStyle.Plain));
        Assert.Equal("random(start, end)", CatalogSymbol("random").Property!.GetDisplaySignature(PropertyCallStyle.Plain));
        Assert.Equal("randomInt(start, end)", CatalogSymbol("randomInt").Property!.GetDisplaySignature(PropertyCallStyle.Plain));
        Assert.Equal("sqrt(x)", CatalogSymbol("sqrt").Property!.GetDisplaySignature(PropertyCallStyle.Plain));
        Assert.Equal("exp(x)", CatalogSymbol("exp").Property!.GetDisplaySignature(PropertyCallStyle.Plain));
        Assert.Equal("pow(x, y)", CatalogSymbol("pow").Property!.GetDisplaySignature(PropertyCallStyle.Plain));
        Assert.Equal("sin(radians)", CatalogSymbol("sin").Property!.GetDisplaySignature(PropertyCallStyle.Plain));
        Assert.Equal("log(value, base)", CatalogSymbol("log").Property!.GetDisplaySignature(PropertyCallStyle.Plain));

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

    [Theory]
    [InlineData("Sin", "sin", "radians")]
    [InlineData("Cos", "cos", "radians")]
    [InlineData("Tan", "tan", "radians")]
    [InlineData("Round", "round", "value", "digits")]
    [InlineData("Log", "log", "value", "base")]
    [InlineData("Exp", "exp", "x")]
    [InlineData("Atan2", "atan2", "y", "x")]
    public void CanonicalAliasAndDotSurfacesShareAuthoritativeParameterNames(
        string canonicalName,
        string aliasName,
        params string[] parameterNames)
    {
        var math = CatalogSymbol("Math");
        var canonical = Assert.Single(math.Members, member => member.Name == canonicalName).Property!;
        var alias = CatalogSymbol(aliasName).Property!;

        Assert.Equal(parameterNames, canonical.GetParameters(PropertyCallStyle.Plain).Select(static parameter => parameter.Name));
        Assert.Equal(parameterNames, alias.GetParameters(PropertyCallStyle.Plain).Select(static parameter => parameter.Name));

        var expectedDotParameters = parameterNames.Skip(1);
        Assert.Equal(expectedDotParameters, canonical.GetParameters(PropertyCallStyle.Dot).Select(static parameter => parameter.Name));
        Assert.Equal(expectedDotParameters, alias.GetParameters(PropertyCallStyle.Dot).Select(static parameter => parameter.Name));
        Assert.StartsWith($"{parameterNames[0]}.{canonicalName}", canonical.GetDisplaySignature(PropertyCallStyle.Dot), StringComparison.Ordinal);
        Assert.StartsWith($"{parameterNames[0]}.{aliasName}", alias.GetDisplaySignature(PropertyCallStyle.Dot), StringComparison.Ordinal);
    }

    [Fact]
    public void PreludeCatalog_AliasDotCallEligibilityAgreesWithRuntime()
    {
        // `v.cos` genuinely runs as `cos(v)` at runtime, so the editor offers
        // the dot surface; the receiver consumes the first parameter.
        var cos = CatalogSymbol("cos").Property!;
        Assert.True(cos.SupportsLexicalDotCall);
        Assert.Equal("radians.cos", cos.FindSignature(PropertyCallStyle.Dot)!.DisplayText);

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
        Assert.Equal("cos(radians)", property.DisplaySignature);
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
        Assert.Null(model.FindPropertyAt(2, 6)!.AliasTarget);
    }

    // ── Alias target metadata (canonical member identity on the alias) ──────

    [Fact]
    public void PreludeCatalog_EveryAliasCarriesItsCanonicalAliasTarget()
    {
        // Descriptor-driven: iterating the registry's member table means a
        // FUTURE alias cannot ship without this metadata — a new descriptor row
        // joins this loop automatically. The display signature must equal the
        // canonical member's own qualified signature, so the two surfaces can
        // never drift.
        var mathMembers = CatalogSymbol("Math").Members;

        foreach (var member in BuiltinRegistry.MathMembers)
        {
            var aliasProperty = CatalogSymbol(member.PreludeAlias).Property!;
            var target = aliasProperty.AliasTarget;
            Assert.NotNull(target);
            Assert.Equal($"Math.{member.Name}", target!.QualifiedName);

            var canonicalProperty = Assert.Single(mathMembers, candidate => candidate.Name == member.Name).Property!;
            Assert.Equal(
                $"Math.{canonicalProperty.GetDisplaySignature(PropertyCallStyle.Plain)}",
                target.DisplaySignature);

            // The canonical member itself is NOT an alias.
            Assert.Null(canonicalProperty.AliasTarget);

            // Constants expose no callable signatures, so no dot-call surface
            // accompanies the alias target; functions keep their dot surface.
            if (member.Kind == MathMemberKind.Constant)
                Assert.Null(aliasProperty.FindSignature(PropertyCallStyle.Dot));
            else
                Assert.NotNull(aliasProperty.FindSignature(PropertyCallStyle.Dot));
        }
    }

    [Fact]
    public void AliasTargetDisplaySignatures_UseAuthoritativeParameterNames()
    {
        Assert.Equal("Math.Sin(radians)", CatalogSymbol("sin").Property!.AliasTarget!.DisplaySignature);
        Assert.Equal("Math.Exp(x)", CatalogSymbol("exp").Property!.AliasTarget!.DisplaySignature);
        Assert.Equal("Math.Atan2(y, x)", CatalogSymbol("atan2").Property!.AliasTarget!.DisplaySignature);
        Assert.Equal("Math.Round(value, digits)", CatalogSymbol("round").Property!.AliasTarget!.DisplaySignature);
        Assert.Equal("Math.Pi", CatalogSymbol("pi").Property!.AliasTarget!.DisplaySignature);
    }

    [Fact]
    public void NonAliasCatalogEntries_CarryNoAliasTarget()
    {
        foreach (var symbol in PreludeCatalog.Symbols)
        {
            if (BuiltinRegistry.MathAliasNames.Contains(symbol.Name, StringComparer.Ordinal))
                continue;

            Assert.Null(symbol.Property?.AliasTarget);
            foreach (var member in symbol.Members)
                Assert.Null(member.Property?.AliasTarget);
        }

        foreach (var symbol in PreludeCatalog.DotIntrinsicSymbols)
            Assert.Null(symbol.Property?.AliasTarget);
    }

    [Fact]
    public void HostOperation_CarriesNoAliasTarget()
    {
        var hostOperations = HostOperations.Create(HostOperation.Create(
            "Sin",
            static (_, _) => new Result.Atom(1),
            "radians"));
        var parseResult = Parser.Parse(
            "Sin(1)",
            new RunOptions { HostOperations = hostOperations });
        Assert.False(
            parseResult.HasErrors,
            string.Join(Environment.NewLine, parseResult.Diagnostics.Select(diagnostic => diagnostic.Message)));

        var model = SemanticModelBuilder.Build(parseResult);
        // Configured host operations currently expose no editor PropertyInfo;
        // in particular, canonical-looking spelling alone cannot fabricate a
        // Math alias target.
        Assert.Null(model.FindPropertyAt(1, 1));
    }

    [Fact]
    public void AliasResolution_CarriesAliasTargetInEveryResolvedSurface()
    {
        // Direct call, bare reference, and lexical dot fallback all resolve to
        // the prelude alias, so each resolved PropertyInfo carries the target.
        var call = BuildModel("sin(1.23)");
        Assert.Equal("Math.Sin(radians)", call.FindPropertyAt(1, 1)!.AliasTarget!.DisplaySignature);

        var bare = BuildModel("F = sin");
        Assert.Equal("Math.Sin(radians)", bare.FindPropertyAt(1, 5)!.AliasTarget!.DisplaySignature);

        var dotFallback = BuildModel("sin(1.23)\nX = 5\nX.sin");
        var dotProperty = dotFallback.FindPropertyAt(3, 3)!;
        Assert.Equal("Math.Sin(radians)", dotProperty.AliasTarget!.DisplaySignature);
        // The dot-preferred presentation variant keeps the target.
        Assert.Equal(PropertyCallStyle.Dot, dotProperty.PreferredCallStyle);
        Assert.Same(dotFallback.FindPropertyAt(1, 1)!.AliasTarget, dotProperty.AliasTarget);

        var constant = BuildModel("pi");
        Assert.Equal("Math.Pi", constant.FindPropertyAt(1, 1)!.AliasTarget!.DisplaySignature);
    }

    [Fact]
    public void ShadowedOrCanonicalResolution_CarriesNoAliasTarget()
    {
        // A user-declared `sin` is an ordinary neutral callable.
        var shadowed = BuildModel("sin(x) = x * 2\nsin(1.23)");
        Assert.Null(shadowed.FindPropertyAt(2, 1)!.AliasTarget);

        // The canonical structural spelling is not an alias.
        var canonical = BuildModel("Math.Sin(1.23)");
        Assert.Null(canonical.FindPropertyAt(1, 6)!.AliasTarget);

        // Opened canonical members are not aliases either.
        var opened = BuildModel("open Math\nSin(1.23)");
        Assert.Null(opened.FindPropertyAt(2, 1)!.AliasTarget);

        // A structural member spelled like an alias wins dot resolution and
        // stays neutral.
        var structural = BuildModel("Obj = { public sin(x) = x }\nObj.sin(1)");
        Assert.Null(structural.FindPropertyAt(2, 5)!.AliasTarget);

        // A user callable selected by lexical dot fallback remains the user's
        // symbol; the alias spelling alone never manufactures target metadata.
        var shadowedFallback = BuildModel("sin(x) = x * 2\nX = 5\nX.sin");
        Assert.Null(shadowedFallback.FindPropertyAt(3, 3)!.AliasTarget);

        // Parameters have no property metadata, so parameter shadowing cannot
        // inherit the prelude alias target either.
        var parameter = BuildModel("F(sin, x) = x.sin\nF({ 1 }, 2)");
        Assert.Equal(
            IdentifierClassification.ExplicitParameterReference,
            ResolutionAt(parameter, 1, 15).Classification);
        Assert.Null(parameter.FindPropertyAt(1, 15));
    }

    [Fact]
    public void OpenProvidedAliasSpelling_LosesToTheDirectPreludeAlias()
    {
        // Direct-beats-open, mirroring OpenedProvider_DoesNotOverrideDirectPreludeAlias
        // on the evaluator side: bare `sin` under `open Lib` still resolves to
        // the prelude alias, so the resolved property keeps its alias target.
        var model = BuildModel("open Lib\nLib = { public sin(x) = 42 }\nsin(1)");
        Assert.Equal("Math.Sin(radians)", model.FindPropertyAt(3, 1)!.AliasTarget!.DisplaySignature);
    }

    [Fact]
    public void RemovedEulerNamesCarryNoAliasMetadata()
    {
        var bare = BuildModel("e");
        Assert.Equal(IdentifierClassification.ImplicitParameterReference, ResolutionAt(bare, 1, 1).Classification);
        Assert.Null(bare.FindPropertyAt(1, 1));

        var qualified = BuildModel("Math.E");
        Assert.Equal(IdentifierClassification.ImplicitParameterReference, ResolutionAt(qualified, 1, 6).Classification);
        Assert.Null(qualified.FindPropertyAt(1, 6));
    }

    [Fact]
    public void AliasTarget_PublicApiShapeSerializationAndRecordSemanticsAreIntentional()
    {
        var aliasProperty = CatalogSymbol("sin").Property!;
        var target = aliasProperty.AliasTarget!;

        var property = typeof(PropertyInfo).GetProperty(nameof(PropertyInfo.AliasTarget));
        Assert.NotNull(property);
        Assert.True(property!.GetMethod!.IsPublic);
        Assert.True(property.SetMethod!.IsPublic);
        Assert.Contains(typeof(System.Runtime.CompilerServices.IsExternalInit),
            property.SetMethod.ReturnParameter.GetRequiredCustomModifiers());
        Assert.Equal(
            System.Reflection.NullabilityState.Nullable,
            new System.Reflection.NullabilityInfoContext().Create(property).ReadState);

        Assert.True(typeof(PropertyAliasTargetInfo).IsPublic);
        Assert.True(typeof(PropertyAliasTargetInfo).IsSealed);
        Assert.Equal(
            [nameof(PropertyAliasTargetInfo.DisplaySignature), nameof(PropertyAliasTargetInfo.QualifiedName)],
            typeof(PropertyAliasTargetInfo).GetProperties()
                .Select(static candidate => candidate.Name)
                .OrderBy(static name => name, StringComparer.Ordinal));

        // The immutable target is value-like and participates intentionally in
        // PropertyInfo record equality/hashing. Dot-presentation record copies
        // preserve the exact target object.
        var equalTarget = new PropertyAliasTargetInfo(target.QualifiedName, target.DisplaySignature);
        Assert.Equal(target, equalTarget);
        Assert.Equal(target.GetHashCode(), equalTarget.GetHashCode());
        Assert.Same(target, aliasProperty.WithPreferredCallStyle(PropertyCallStyle.Dot).AliasTarget);

        var withoutTarget = aliasProperty with { AliasTarget = null };
        Assert.NotEqual(aliasProperty, withoutTarget);
        var dictionary = new Dictionary<PropertyInfo, string>
        {
            [aliasProperty] = "alias",
            [withoutTarget] = "ordinary",
        };
        Assert.Equal(2, dictionary.Count);

        var json = JsonSerializer.Serialize(aliasProperty);
        var roundTripped = JsonSerializer.Deserialize<PropertyInfo>(json);
        Assert.NotNull(roundTripped);
        Assert.Equal(target, roundTripped!.AliasTarget);
        Assert.Equal(aliasProperty.Name, roundTripped.Name);
        Assert.Equal(aliasProperty.DisplaySignature, roundTripped.DisplaySignature);
    }
}
