using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// Q-19 — RESOLVED BY DECISION 2026-10-06 — D-I: an <c>open</c> list counts the PROVIDERS its
/// targets resolve to, by the language's semantic provider identity (the declaration and its
/// declaring scope — NEED-04's callable identity), never by spelling or position. Written targets
/// that resolve to one provider count once (<c>open M, M</c>, <c>open M, (M)</c>,
/// <c>open Sub, Lib.Sub</c> for one declaration); distinct providers stay distinct however equal
/// their members, values, or text (two written blocks, two declarations, a member alias). Every
/// layer agrees: the evaluator (<c>Evaluator.ResolveAllOpens</c>), elaborated lookup and with it
/// detection and the editor (<c>ElaboratedScopeLookup.ResolveOpenProvider</c>), exposure
/// settlement, the exposure summary channel, implicit-argument resolution, and Lean
/// (<c>resolveAllOpens</c>, CoreTests <c>OpenProviderIdentity</c>). Runtime cases run on the six
/// routes (<see cref="SixRouteAgreement"/>).
/// </summary>
public class OpenProviderIdentityTests
{
    private const string SubInsideLib = "Lib = {\n    public Sub = {\n        public X = 1\n    }\n    public R = {\n        open §\n        X\n    }\n}\nLib.R";

    private static string SubInside(string opens) => SubInsideLib.Replace("§", opens, StringComparison.Ordinal);

    /// <summary>name, source, expected value.</summary>
    public static TheoryData<string, string, string> OneProviderMatrix() => new()
    {
        { "same spelling twice", "open M, M\nM = {\n    public X = 1\n}\nX", "1" },
        { "redundant group is the target", "open M, (M)\nM = {\n    public X = 1\n}\nX", "1" },
        { "two spellings of one declaration", SubInside("Sub, Lib.Sub"), "1" },
        { "two spellings, reversed", SubInside("Lib.Sub, Sub"), "1" },
        { "one spelling (control)", SubInside("Sub"), "1" },
        { "dotted path twice", "open Lib.Sub, Lib.Sub\nLib = {\n    public Sub = {\n        public X = 1\n    }\n}\nX", "1" },
        { "three spellings of one declaration", SubInside("Sub, Lib.Sub, (Sub)"), "1" },
        {
            "two spellings beside a distinct provider of another name",
            "Lib = {\n    public Sub = {\n        public X = 1\n    }\n    public R = {\n        open Sub, Other, Lib.Sub\n        X + Y\n    }\n}\nOther = {\n    public Y = 10\n}\nLib.R",
            "11"
        },
        {
            "a property reading a namespace provides nothing",
            "open Lib.Sub, Sub\nLib = {\n    public Sub = {\n        public X = 1\n    }\n}\nSub = Lib.Sub\nX",
            "1"
        },
        {
            "two reads of one provider set",
            "Lib = {\n    public Sub = {\n        public X = 4\n    }\n    public R = {\n        open Sub, Lib.Sub\n        X * 10\n    }\n}\nLib.R + Lib.R",
            "80"
        },
    };

    [Theory]
    [MemberData(nameof(OneProviderMatrix))]
    public async Task OneProvider_ThroughEverySpelling_IsOneProvider(string name, string source, string expected)
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.True(observation.Kind == "ok", $"{name}: {observation}");
        Assert.Equal(expected, observation.Value);
    }

    /// <summary>name, source: distinct providers whose members, text or values coincide.</summary>
    public static TheoryData<string, string> DistinctProviderMatrix() => new()
    {
        { "two identical written blocks", "open { public X = 1 }, { public X = 1 }\nX" },
        { "two declarations with identical text", "open L1, L2\nL1 = {\n    public X = 1\n}\nL2 = {\n    public X = 1\n}\nX" },
        { "one provider's member aliases the other's", "open A, B\nA = {\n    public X(v) = v\n}\nB = {\n    public X = A.X\n}\nX(1)" },
        { "the alias first", "open B, A\nA = {\n    public X(v) = v\n}\nB = {\n    public X = A.X\n}\nX(1)" },
    };

    [Theory]
    [MemberData(nameof(DistinctProviderMatrix))]
    public void DistinctProviders_StayDistinct_HoweverEqualTheirMembers(string name, string source)
    {
        // Provider identity is the provider's declaration, never its member set, text, values or the
        // identity of one requested member (Q-19): a written X they both provide is ambiguous (Q-29 A-U).
        var diagnostic = Assert.Single(SourceProvenance.ExpectFrontEndError(source));
        Assert.True(diagnostic.Code == DiagnosticCode.AmbiguousOpen, $"{name}: {diagnostic.Code} {diagnostic.Message}");
    }

    [Fact]
    public async Task AMemberAlias_IsItsTargetsCallable_WhenOneProviderOffersIt()
    {
        // The control for the alias row above: opened alone, B's alias is A's callable.
        var observation = await SixRouteAgreement.OnEveryRouteAsync("open B\nA = {\n    public X(v) = v\n}\nB = {\n    public X = A.X\n}\nX(1)");
        Assert.Equal("1", observation.Value);
    }

    [Fact]
    public async Task OpenOrder_NeverDecidesTheProviderSet()
    {
        foreach (var spellings in new[] { "Sub, Lib.Sub", "Lib.Sub, Sub" })
        {
            var observation = await SixRouteAgreement.OnEveryRouteAsync(SubInside(spellings));
            Assert.Equal("1", observation.Value);
        }
    }

    [Fact]
    public async Task ImplicitArgumentResolution_LiftsThroughOneProviderReachedTwice()
    {
        // The resolver's open lookup counts providers by identity too: `F` through two spellings of
        // one provider is F's signature, so the formula lifts F's parameter (K(x) = F(x) + 1).
        const string source = "Lib = {\n    public Sub = {\n        public F(x) = x * 10\n    }\n    public R = {\n        open Sub, Lib.Sub\n        K = F + 1\n        K(4)\n    }\n}\nLib.R";
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("41", observation.Value);

        var parsed = SourceProvenance.ParseValid(source);
        var lib = Assert.IsType<Algorithm.User>(parsed.Root.Properties.Single(static p => p.Name == "Lib").Value);
        var r = Assert.IsType<Algorithm.User>(lib.Properties.Single(static p => p.Name == "R").Value);
        var k = Assert.IsType<Algorithm.User>(r.Properties.Single(static p => p.Name == "K").Value);
        Assert.Equal(["x"], k.Params);
    }

    [Fact]
    public async Task Exposure_ChargesOneProviderReachedTwice_SoACapturingMemberStaysLocal()
    {
        // `X` reads the capturing `Sub.X` through two spellings of ONE provider, so `R` requires
        // Outer's `p` (local-only): each activation reads its own value, never a run-cached one.
        const string source = "Outer(p) = {\n    Lib = {\n        public Sub = {\n            public X = p\n        }\n        public R = {\n            open Sub, Lib.Sub\n            X\n        }\n    }\n    Lib.R\n}\nOuter(5), Outer(6)";
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("S[5, 6]", observation.Value);

        var parsed = SourceProvenance.ParseValid(source);
        var outer = Assert.IsType<Algorithm.User>(parsed.Root.Properties.Single(static p => p.Name == "Outer").Value);
        var lib = Assert.IsType<Algorithm.User>(outer.Properties.Single(static p => p.Name == "Lib").Value);
        var r = lib.Properties.Single(static p => p.Name == "R");
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, r.Exposure);
    }

    [Fact]
    public async Task Exposure_ChargesOneProviderWrittenTwice()
    {
        const string source = "Outer(p) = {\n    open Lib, Lib\n    Lib = {\n        public X = p\n    }\n    Y = X + 0\n    Y\n}\nOuter(5), Outer(6)";
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("S[5, 6]", observation.Value);

        var outer = Assert.IsType<Algorithm.User>(SourceProvenance.ParseValid(source).Root.Properties.Single(static p => p.Name == "Outer").Value);
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, outer.Properties.Single(static p => p.Name == "Y").Exposure);
    }

    [Fact]
    public async Task Exposure_SettlesOneProviderReachedFromTwoLevels_Once()
    {
        // Inside `Lib`, `Sub` is declared at the opener's own level (settled in place) while `Lib.Sub`
        // is headed by `Outer`'s `Lib` (settled farther out): one declaration either way, so `R` reads
        // the capturing `X` through ONE provider and requires Outer's `p` (local-only).
        const string source = "Outer(p) = {\n    Lib = {\n        open Sub, Lib.Sub\n        public Sub = {\n            public X = p\n        }\n        public R = X + 0\n    }\n    Lib.R\n}\nOuter(5), Outer(6)";
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("S[5, 6]", observation.Value);

        var outer = Assert.IsType<Algorithm.User>(SourceProvenance.ParseValid(source).Root.Properties.Single(static p => p.Name == "Outer").Value);
        var lib = Assert.IsType<Algorithm.User>(outer.Properties.Single(static p => p.Name == "Lib").Value);
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, lib.Properties.Single(static p => p.Name == "R").Exposure);
    }

    [Fact]
    public void Editor_ResolvesANameOfOneProviderReachedTwice_ToItsDeclaration()
    {
        // `X` in R's body (line 7) resolves to Sub's declaration of X (line 3, column 16), as the
        // evaluator selects it — never Unresolved because the provider was reached twice.
        var source = SubInside("Sub, Lib.Sub");
        var model = SemanticModelBuilder.Build(SourceProvenance.ParseValid(source).Parsed);
        var resolution = model.FindResolutionAt(new SourcePosition(7, 9));
        Assert.NotNull(resolution);
        Assert.Equal(IdentifierClassification.PropertyReference, resolution!.Classification);
        Assert.Equal(new SourcePosition(3, 16), resolution.ResolvedDeclaration?.Span.Start);
    }

    [Fact]
    public void ElaboratedLookup_CountsProviders_NotTargets()
    {
        var root = SourceProvenance.ParseValid(SubInside("Sub, Lib.Sub, (Sub)")).Root;
        var lib = Assert.IsType<Algorithm.User>(root.Properties.Single(static p => p.Name == "Lib").Value);
        var r = Assert.IsType<Algorithm.User>(lib.Properties.Single(static p => p.Name == "R").Value);
        var libScope = ElaboratedScopeLookup.CreateScope(lib, ElaboratedScopeLookup.CreateScope(root));
        var rScope = ElaboratedScopeLookup.CreateScope(r, libScope);

        var providers = rScope.GetResolvedOpenProviders();
        Assert.Single(providers);
        Assert.Single(ElaboratedScopeLookup.LookupOpenPropertyMatches(rScope, "X"));

        // The identity is the declaration in its declaring scope: the two spellings agree, a
        // structurally equal block declared elsewhere does not.
        var viaName = ElaboratedScopeLookup.ResolveOpenProvider(rScope, new Expr.Resolve("Sub"))!.Value.Identity;
        var viaPath = ElaboratedScopeLookup.ResolveOpenProvider(rScope, new Expr.DotCall(new Expr.Resolve("Lib"), "Sub", null))!.Value.Identity;
        Assert.Equal(viaName, viaPath);
        var twin = ElaboratedScopeLookup.ResolveOpenProvider(rScope, new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [new Property("X", new Algorithm.User(null, [], [], [], [new Expr.Num(1)]))], [])))!.Value.Identity;
        Assert.NotEqual(viaName, twin);
    }
}
