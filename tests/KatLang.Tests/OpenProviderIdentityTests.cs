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
            // M4★ OD-C: the unbraced reference opens its target under the TARGET's provider identity.
            "a reference to a namespace is that namespace's provider",
            "open Lib.Sub, Sub\nLib = {\n    public Sub = {\n        public X = 1\n    }\n}\nSub = Lib.Sub\nX",
            "1"
        },
        {
            // A braced carrier is a provider of its OWN public declarations only (none here).
            "a carrier of a namespace provides only its own declarations",
            "open Lib.Sub, Sub\nLib = {\n    public Sub = {\n        public X = 1\n    }\n}\nSub = { Lib.Sub }\nX",
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

    [Fact]
    public async Task AReferenceAndACarrierOfOneNamespace_DifferAsProviders_WhenOpenedAlone()
    {
        const string Lib = "Lib = {\n    public Sub = {\n        public X = 1\n    }\n}\n";
        // The unbraced reference provides its target's names (M4★ OD-C) ...
        var reference = await SixRouteAgreement.OnEveryRouteAsync("open Sub\n" + Lib + "Sub = Lib.Sub\nX");
        Assert.Equal("ok", reference.Kind);
        Assert.Equal("1", reference.Value);
        // ... while the braced carrier provides only its own public declarations, so X stays an
        // implicit parameter of the root.
        var carrier = await SixRouteAgreement.OnEveryRouteAsync("open Sub\n" + Lib + "Sub = { Lib.Sub }\nX");
        Assert.Equal("err", carrier.Kind);
        Assert.Contains("UnresolvedImplicitParams", carrier.Errors[0], StringComparison.Ordinal);
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
        // R's lone row X makes it a forwarding carrier of X (M4★): it owns its opens, so its scope is its own.
        var r = Assert.IsType<Algorithm.Alias>(lib.Properties.Single(static p => p.Name == "R").Value);
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

    // ── The runtime declaration index (implementation-only, November 2026) ─────────────────────
    // `Evaluator.ResolveAllOpens` resolves a consulted level's targets on every read and counts its
    // providers by comparing each target only with the accepted targets of its OWN declaration
    // (`Evaluator.DeduplicateResolvedProviders`). The former scan compared every target with every
    // accepted one: R reads consulting a level of K distinct declarations made R·K(K−1)/2 identity
    // comparisons, cubic when R = K. Counts come from the run's EvaluationObservations on a prepared
    // root, on the synchronous route and the forced async twin alike (OpenProviderIndexing).

    /// <summary>
    /// <c>open M0, …, M{K−1}</c> with <c>Mi = { public Vi = i }</c> (or <c>public Fi(x) = x + i</c>)
    /// and one row listing every opened name — or, as the control, every qualified member.
    /// </summary>
    private static string WideOpen(int width, bool callable, bool qualified)
    {
        var names = Enumerable.Range(0, width).ToArray();
        var declarations = string.Concat(names.Select(i => callable
            ? $"M{i} = {{ public F{i}(x) = x + {i} }}\n"
            : $"M{i} = {{ public V{i} = {i} }}\n"));
        var reads = names.Select(i => (qualified ? $"M{i}." : "") + (callable ? $"F{i}(0)" : $"V{i}"));
        return $"open {string.Join(", ", names.Select(i => $"M{i}"))}\n{declarations}[{string.Join(", ", reads)}]";
    }

    [Theory]
    [InlineData(1)]
    [InlineData(2)]
    [InlineData(4)]
    [InlineData(8)]
    [InlineData(9)]
    [InlineData(16)]
    [InlineData(32)]
    [InlineData(64)]
    public async Task DistinctDeclarations_AreIndexedWithoutAnyIdentityComparison(int width)
    {
        var expected = $"ok L[{string.Join(", ", Enumerable.Range(0, width))}]";
        // The narrow path scans declaration keys (at most 28 per level); a wider level hashes them.
        long keyComparisonsPerLevel = width <= Evaluator.OpenProviderLinearIndexLimit ? width * (width - 1) / 2 : 0;
        foreach (var callable in new[] { false, true })
        {
            // Every read is one lexical lookup that consults the root's open level (value reads, and
            // callee resolution as the callable control): K levels of K targets each.
            var opened = await OpenProviderIndexing.OnBothRoutesAsync(WideOpen(width, callable, qualified: false));
            Assert.Equal(new OpenProviderIndexing.Observation(expected, width, (long)width * width, width * keyComparisonsPerLevel, 0, 0), opened);

            // The qualified control reads the same members structurally and consults no open level.
            var qualified = await OpenProviderIndexing.OnBothRoutesAsync(WideOpen(width, callable, qualified: true));
            Assert.Equal(new OpenProviderIndexing.Observation(expected, 0, 0, 0, 0, 0), qualified);
        }
    }

    [Fact]
    public async Task ProviderIndexWorkPerConsultedLevel_GrowsLinearlyWithTheWidth()
    {
        // K and 2K over the hashed path: the work per consulted level is the K index entries alone
        // (the pairwise scan added K(K−1)/2 identity comparisons per level, 2,016 at K = 64).
        long? previous = null;
        foreach (var width in new[] { 16, 32, 64, 128 })
        {
            var opened = await OpenProviderIndexing.OnBothRoutesAsync(WideOpen(width, callable: false, qualified: false));
            Assert.Equal(width, opened.Levels);
            Assert.Equal(0, opened.IdentityComparisons);
            Assert.Equal(width, opened.WorkPerLevel);
            if (previous is { } half)
                Assert.Equal(2 * half, opened.WorkPerLevel);
            previous = opened.WorkPerLevel;
        }
    }

    /// <summary>
    /// A host-built root opening inline blocks: <c>P</c> is ONE declaration pre-wired under the host
    /// levels <paramref name="pLevels"/> (one block per entry, at that position), every other entry
    /// (<c>null</c>) a distinct declaration of its own. Every block publicly provides <c>Z</c>, so the
    /// read of <c>Z</c> is the evaluator's ambiguity naming EVERY provider of the level in order.
    /// </summary>
    private static Expr OneDeclarationAmongOthers(params ScopeCtx?[] pLevels)
    {
        static Algorithm.User Namespace(int value)
            => new(null, [], [], [new Property("Z", new Algorithm.User(null, [], [], [], [new Expr.Num(value)]), IsPublic: true)], OutputBundle.Empty);

        var p = Namespace(100);
        var opens = pLevels.Select((level, i) => (Expr)new Expr.AlgorithmExpr(level is null ? Namespace(i) : p with { Parent = level })).ToArray();
        return new Expr.AlgorithmExpr(new Algorithm.User(null, [], opens, [], [new Expr.Resolve("Z")]));
    }

    private static string AmbiguityOf(params int[] positions)
        => $"AmbiguousOpen(Z: {string.Join(", ", positions.Select(static i => $"(inline#{i})"))}) @ ";

    [Fact]
    public async Task OneDeclarationUnderDistinctHostLevels_StaysDistinctProviders_OnTheNarrowPath()
    {
        ScopeCtx s1 = new(null, [], []), s2 = new(null, [], []);
        // P@s1, D, P@s2, P@s1, D: the second P@s1 is the first one's provider; P@s2 is another
        // (declaration bucketing never merges distinct declaring scopes).
        var distinct = await OpenProviderIndexing.OnBothRoutesAsync(OneDeclarationAmongOthers(s1, null, s2, s1, null));
        Assert.Contains(AmbiguityOf(0, 1, 2, 4), distinct.Outcome, StringComparison.Ordinal);
        Assert.Equal((1, 5, 7, 2, 0), (distinct.Levels, distinct.Entries, distinct.KeyComparisons, distinct.IdentityComparisons, distinct.CrossDeclarationIdentityComparisons));

        // Control: every P reach under ONE host level object is one provider.
        var same = await OpenProviderIndexing.OnBothRoutesAsync(OneDeclarationAmongOthers(s1, null, s1, s1, null));
        Assert.Contains(AmbiguityOf(0, 1, 4), same.Outcome, StringComparison.Ordinal);
        Assert.Equal((1, 5, 5, 2, 0), (same.Levels, same.Entries, same.KeyComparisons, same.IdentityComparisons, same.CrossDeclarationIdentityComparisons));
    }

    [Fact]
    public async Task OneDeclarationUnderDistinctHostLevels_StaysDistinctProviders_OnTheHashedPath()
    {
        ScopeCtx s1 = new(null, [], []), s2 = new(null, [], []), s3 = new(null, [], []);
        // Twelve targets: P's reaches are compared only with P's accepted reaches, in acceptance
        // order (P@s3 with P@s1 and P@s2; the later P@s2 matches the SECOND accepted reach).
        var distinct = await OpenProviderIndexing.OnBothRoutesAsync(
            OneDeclarationAmongOthers(s1, null, s2, null, s1, null, s3, null, s2, null, null, null));
        Assert.Contains(AmbiguityOf(0, 1, 2, 3, 5, 6, 7, 9, 10, 11), distinct.Outcome, StringComparison.Ordinal);
        Assert.Equal((1, 12, 0, 6, 0), (distinct.Levels, distinct.Entries, distinct.KeyComparisons, distinct.IdentityComparisons, distinct.CrossDeclarationIdentityComparisons));

        var same = await OpenProviderIndexing.OnBothRoutesAsync(
            OneDeclarationAmongOthers(s1, null, s1, null, s1, null, s1, null, s1, null, null, null));
        Assert.Contains(AmbiguityOf(0, 1, 3, 5, 7, 9, 10, 11), same.Outcome, StringComparison.Ordinal);
        Assert.Equal((1, 12, 0, 4, 0), (same.Levels, same.Entries, same.KeyComparisons, same.IdentityComparisons, same.CrossDeclarationIdentityComparisons));
    }

    private const string FallbackThroughOpens =
        "Lib = {\n    public Sub = {\n        public X(v) = v\n    }\n}\nOther = {\n    public X(v) = v + 1\n}\nRef = Lib.Sub\nA = {\n    open §\n    K(q) = q.X\n    K(10)\n}\nA";

    /// <summary>target list, providers of the runtime ambiguity in order (null: one provider, value 10), identity comparisons per level.</summary>
    public static TheoryData<string, string?, int> FirstRepresentativeMatrix() => new()
    {
        { "Lib.Sub, Ref, Other", "Lib.Sub, Other", 1 },
        { "Ref, Lib.Sub, Other", "Ref, Other", 1 },
        { "Other, Ref, Lib.Sub", "Other, Ref", 1 },
        { "Ref, Other, Lib.Sub, Ref", "Ref, Other", 1 },
        { "Lib.Sub, Ref", null, 1 },
        { "Lib.Sub, Other", "Lib.Sub, Other", 0 },
    };

    [Theory]
    [MemberData(nameof(FirstRepresentativeMatrix))]
    public async Task TheFirstRepresentative_NamesTheProvider_AndDeclarationsSkipEachOther(string targets, string? providers, int identityPerLevel)
    {
        // A transparent reference and a dotted path to one declaration are one provider named by its
        // first target; the runtime ambiguity of a fallback the receiver decides (`q.X`) lists the
        // providers in order. Only the two reaches of Sub's declaration are ever compared.
        var source = FallbackThroughOpens.Replace("§", targets, StringComparison.Ordinal);
        var observed = await OpenProviderIndexing.OnBothRoutesAsync(source);
        if (providers is null)
            Assert.Equal("ok 10", observed.Outcome);
        else
            Assert.Contains($"AmbiguousOpen(X: {providers}) @ ", observed.Outcome, StringComparison.Ordinal);
        Assert.Equal(1, observed.Levels);
        Assert.Equal(identityPerLevel, observed.IdentityComparisons);
        Assert.Equal(0, observed.CrossDeclarationIdentityComparisons);

        var engine = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal(providers is null ? "ok" : "err", engine.Kind);
    }

    [Fact]
    public async Task EqualInlineProviders_AreTwoDeclarations_NeverCompared()
    {
        const string source = "A = {\n    open { public X(v) = 101 }, { public X(v) = 101 }\n    K(q) = q.X\n    K(10)\n}\nA";
        var observed = await OpenProviderIndexing.OnBothRoutesAsync(source);
        Assert.Contains("AmbiguousOpen(X: (inline#0), (inline#1)) @ ", observed.Outcome, StringComparison.Ordinal);
        Assert.Equal((1, 2, 1, 0), (observed.Levels, observed.Entries, observed.KeyComparisons, observed.IdentityComparisons));
    }
}
