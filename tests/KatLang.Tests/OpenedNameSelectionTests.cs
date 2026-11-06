using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// The adapters' one opened-name policy (<see cref="ElaboratedScopeLookup.SelectFirstOpenLevel"/>): the first open
/// level that provides a name decides it, and <c>LookupSingleOpenMember</c>, <c>LookupOpenPropertyMatches</c> and
/// <c>FindAmbiguousOpenProviders</c> are projections of that selection. Every expectation is written by hand from
/// the source (the declaring body, provider order, deciding level), never by comparing two projections.
/// Elsewhere: Q-29's diagnostic matrix is <see cref="StaticAmbiguousOpenTests"/>, provider identity across layers
/// <see cref="OpenProviderIdentityTests"/>, shared indexes <see cref="OpenMemberIndexSharingTests"/>, and the deferred
/// and available frames <c>BranchLazyModuleLoadingTests.SemanticModel_Deferred*</c> and <c>StandaloneScopeRecoveryTests</c>.
/// </summary>
public class OpenedNameSelectionTests
{
    private const string Libraries =
        "A = {\n    public X = 1\n    public OnlyA = 2\n    0\n}\n"
        + "B = {\n    public X = 3\n    0\n}\n"
        + "C = {\n    public X = 4\n    public Far = 5\n    0\n}\n"
        + "Empty = {\n    public Other = 6\n    0\n}\n";

    private static Algorithm Resolved(string source) => SourceProvenance.ParseValid(source).Root;

    private static Algorithm Body(Algorithm owner, string name)
        => owner.Properties.Single(property => property.Name == name).Value;

    private static Property Member(Algorithm root, string body, string name)
        => Body(root, body).Properties.Single(property => property.Name == name);

    /// <summary>The completed level of the body at <paramref name="path"/>, on a chain rooted at the prelude.</summary>
    private static ElaboratedPropertyScope LevelAt(Algorithm root, params string[] path)
    {
        var facts = root.CompletedStructure!.Facts;
        var prelude = ElaboratedScopeLookup.CreateScope(facts.Prelude, completedContext: facts.Context(facts.PreludeKey));
        var scope = ElaboratedScopeLookup.CreateScope(root, prelude, memberIndexes: new OpenMemberIndexCache(null));
        var body = root;
        foreach (var name in path)
        {
            body = Body(body, name);
            scope = ElaboratedScopeLookup.CreateScope(body, scope);
        }

        return scope;
    }

    /// <summary>A valid program whose level <c>Outer.Inner</c> and its parent <c>Outer</c> open the given targets.</summary>
    private static Algorithm ValidNested(string outerOpens, string innerOpens, string libraries = Libraries)
        => Resolved(libraries + $"Outer = {{\n    open {outerOpens}\n    Inner = {{\n        open {innerOpens}\n        7\n    }}\n    0\n}}\n0");

    private static ElaboratedPropertyScope InnerLevel(Algorithm root) => LevelAt(root, "Outer", "Inner");

    [Fact]
    public void NoProvider_IsEmptyInEveryProjection()
    {
        var root = ValidNested("Empty", "Empty");
        var inner = InnerLevel(root);

        var selection = ElaboratedScopeLookup.SelectFirstOpenLevel(inner, "X");

        Assert.Equal(0, selection.Count);
        Assert.Null(selection.Level);
        Assert.Null(selection.Single);
        Assert.Empty(selection.Hits());
        Assert.Empty(selection.Providers());
        Assert.Null(ElaboratedScopeLookup.LookupSingleOpenMember(inner, "X"));
        Assert.Empty(ElaboratedScopeLookup.LookupOpenPropertyMatches(inner, "X"));
        Assert.Null(ElaboratedScopeLookup.FindAmbiguousOpenProviders(inner, "X"));
    }

    [Fact]
    public void AnOuterLevelDecides_WhenInnerLevelsProvideNothing()
    {
        var root = ValidNested("C", "Empty");
        var inner = InnerLevel(root);

        var selection = ElaboratedScopeLookup.SelectFirstOpenLevel(inner, "Far");

        Assert.Same(inner.Parent, selection.Level);
        Assert.Same(Body(root, "C"), selection.Single!.Value.Provider.Target);
        Assert.Same(Member(root, "C", "Far"), selection.Single!.Value.Hit.Property);
        var opened = ElaboratedScopeLookup.LookupSingleOpenMember(inner, "Far")!.Value;
        Assert.Same(Member(root, "C", "Far"), opened.Hit.Property);
        Assert.Same(Member(root, "C", "Far"), opened.MemberLevel.TryLookupOwnProperty("Far")!.Value.Property);
        Assert.Same(Member(root, "C", "Far"), Assert.Single(ElaboratedScopeLookup.LookupOpenPropertyMatches(inner, "Far")).Property);
    }

    [Fact]
    public void ANearUniqueMatch_HidesAFarAmbiguity()
    {
        var root = ValidNested("A, B", "C");
        var inner = InnerLevel(root);

        Assert.Same(inner, ElaboratedScopeLookup.SelectFirstOpenLevel(inner, "X").Level);
        var opened = ElaboratedScopeLookup.LookupSingleOpenMember(inner, "X")!.Value;
        Assert.Same(Member(root, "C", "X"), opened.Hit.Property);
        // The member's level is C's body at C's declaring level, not the occurrence's or the opener's.
        Assert.Same(Member(root, "C", "X"), opened.MemberLevel.TryLookupOwnProperty("X")!.Value.Property);
        Assert.Same(inner.Root, opened.MemberLevel.Root);
        Assert.Null(opened.MemberLevel.TryLookupOwnProperty("OnlyA"));
        Assert.Same(Member(root, "C", "X"), Assert.Single(ElaboratedScopeLookup.LookupOpenPropertyMatches(inner, "X")).Property);
        Assert.Null(ElaboratedScopeLookup.FindAmbiguousOpenProviders(inner, "X"));
        Assert.Equal("ok raw=4 n=1", SemanticExplorerHarness.Observe("selection.near-unique",
            Libraries + "Outer = {\n    open A, B\n    Inner = {\n        open C\n        X\n    }\n    Inner\n}\nOuter").Neutral);
    }

    [Theory]
    [InlineData("A, B", "A", "B")]
    [InlineData("B, A", "B", "A")]
    public void ANearAmbiguity_NeverFallsThroughToAFarUniqueMatch(string opens, string first, string second)
    {
        var root = ValidNested("C", opens);
        var inner = InnerLevel(root);

        var selection = ElaboratedScopeLookup.SelectFirstOpenLevel(inner, "X");

        Assert.Same(inner, selection.Level);
        Assert.Equal(2, selection.Count);
        Assert.Null(selection.Single);
        Assert.Null(ElaboratedScopeLookup.LookupSingleOpenMember(inner, "X"));
        Assert.Equal(new[] { Member(root, first, "X"), Member(root, second, "X") },
            ElaboratedScopeLookup.LookupOpenPropertyMatches(inner, "X").Select(hit => hit.Property));
        Assert.Equal(new[] { Body(root, first), Body(root, second) },
            ElaboratedScopeLookup.FindAmbiguousOpenProviders(inner, "X")!.Select(provider => provider.Target));
        var diagnostic = Assert.Single(SourceProvenance.ExpectFrontEndError(
            Libraries + $"Outer = {{\n    open C\n    Inner = {{\n        open {opens}\n        X\n    }}\n    Inner\n}}\nOuter"));
        Assert.Equal(DiagnosticCode.AmbiguousOpen, diagnostic.Code);
    }

    [Fact]
    public void TheSelectionIsOpenOnly_LexicalPrecedenceStaysAtEachCallersBoundary()
    {
        // An outer direct declaration: open-only matching still sees the providers, the lexical callers stop first.
        var root = Resolved(Libraries + "X = 9\nOuter = {\n    Inner = {\n        open A, B\n        7\n    }\n    0\n}\n0");
        var inner = InnerLevel(root);
        Assert.Equal(2, ElaboratedScopeLookup.SelectFirstOpenLevel(inner, "X").Count);
        Assert.Equal(2, ElaboratedScopeLookup.LookupOpenPropertyMatches(inner, "X").Count);
        Assert.Same(root.Properties.Single(property => property.Name == "X"),
            Assert.Single(ElaboratedScopeLookup.LookupLexicalPropertyMatches(inner, "X")).Property);
        Assert.Null(ElaboratedScopeLookup.FindAmbiguousOpenProviders(inner, "X"));

        // The prelude is the outermost direct level.
        var prelude = Resolved("L = {\n    public pi = 1\n    0\n}\nM = {\n    public pi = 2\n    0\n}\nU = {\n    open L, M\n    7\n}\n0");
        var user = LevelAt(prelude, "U");
        Assert.Equal(2, ElaboratedScopeLookup.SelectFirstOpenLevel(user, "pi").Count);
        Assert.Null(ElaboratedScopeLookup.FindAmbiguousOpenProviders(user, "pi"));
        Assert.Equal(new[] { user.Root.TryLookupOwnProperty("pi")!.Value.Property },
            ElaboratedScopeLookup.LookupLexicalPropertyMatches(user, "pi").Select(hit => hit.Property));

        // A chain without any open answers null without touching a provider.
        var closed = LevelAt(Resolved("U = {\n    V = 1\n    7\n}\n0"), "U");
        Assert.False(closed.HasOpensInChain);
        Assert.Null(ElaboratedScopeLookup.FindAmbiguousOpenProviders(closed, "V"));
    }

    [Fact]
    public void AnOwnedParameter_IsExcludedByTheCaller_NotByTheSelection()
    {
        var root = Resolved(Libraries + "F(X) = {\n    open A\n    Y = 1\n    Y + X\n}\nF(1)");
        var level = LevelAt(root, "F");

        Assert.Same(Member(root, "A", "X"), ElaboratedScopeLookup.LookupSingleOpenMember(level, "X")!.Value.Hit.Property);
        Assert.Equal(StaticStructuralMemberProviderKind.RuntimeParameter,
            ElaboratedScopeLookup.CompletedReceiver(new Expr.Resolve("X"), level).Kind);
        Assert.Equal(OwnedDeclarationKind.Parameter,
            ElaboratedScopeLookup.SelectOwnedDeclaration(level, "X", ElaboratedScopeLookup.OwnParameterBindings.Instance).Kind);
        // With no owner, the receiver reads the opened member at its own declaring level.
        var opened = ElaboratedScopeLookup.CompletedReceiver(new Expr.Resolve("OnlyA"), level);
        Assert.Equal(StaticStructuralMemberProviderKind.KnownAlgorithm, opened.Kind);
        Assert.Same(Member(root, "A", "OnlyA").Value, opened.Algorithm);
    }

    [Theory]
    [InlineData("Lib, Lib", 1)]
    [InlineData("Lib, Alias", 1)]
    [InlineData("Alias, Lib, Alias", 1)]
    [InlineData("Lib, Twin", 2)]
    public void ProvidersCountByIdentity_NeverByEqualMembersOrSpelling(string opens, int expected)
    {
        var root = Resolved("Lib = {\n    public X = 1\n    0\n}\nAlias = Lib\nTwin = {\n    public X = 1\n    0\n}\n"
            + $"U = {{\n    open {opens}\n    7\n}}\n0");
        var level = LevelAt(root, "U");

        var selection = ElaboratedScopeLookup.SelectFirstOpenLevel(level, "X");

        Assert.Equal(expected, selection.Count);
        Assert.Same(Body(root, "Lib"), selection[0].Provider.Target);
        Assert.Same(Member(root, "Lib", "X"), selection[0].Hit.Property);
        if (expected == 1)
        {
            Assert.Null(ElaboratedScopeLookup.FindAmbiguousOpenProviders(level, "X"));
            Assert.NotNull(ElaboratedScopeLookup.LookupSingleOpenMember(level, "X"));
        }
        else
        {
            Assert.Same(Body(root, "Twin"), selection[1].Provider.Target);
            Assert.Equal(2, ElaboratedScopeLookup.FindAmbiguousOpenProviders(level, "X")!.Count);
            Assert.Null(ElaboratedScopeLookup.LookupSingleOpenMember(level, "X"));
        }
    }

    [Fact]
    public void OnlyPublicMembersParticipate_AndExposureTakesNoPartInSelection()
    {
        // A private member is no match, so the search continues outward.
        var root = ValidNested("C", "Private", Libraries + "Private = {\n    Far = 8\n    0\n}\n");
        var inner = InnerLevel(root);
        Assert.Same(inner.Parent, ElaboratedScopeLookup.SelectFirstOpenLevel(inner, "Far").Level);
        Assert.Same(Member(root, "C", "Far"), ElaboratedScopeLookup.LookupSingleOpenMember(inner, "Far")!.Value.Hit.Property);

        // A public member whose exposure is local-only is selected exactly like an exported one.
        var host = Resolved("Host(a) = {\n    Lib = {\n        public V = a\n        0\n    }\n    Use = {\n        open Lib\n        V\n    }\n    Use\n}\nHost(1)");
        var use = LevelAt(host, "Host", "Use");
        var local = ElaboratedScopeLookup.LookupSingleOpenMember(use, "V")!.Value;
        Assert.Same(Body(Body(host, "Host"), "Lib").Properties.Single(), local.Hit.Property);
        Assert.NotEqual(PropertyExposure.Exported, local.Hit.Property.Exposure);
    }

    [Fact]
    public void TheMemberLevel_IsTheProvidersGenuineDeclaringContext()
    {
        var root = Resolved("Host = {\n    Lib = {\n        public V = 1\n        0\n    }\n    Use = {\n        open Lib\n        7\n    }\n    0\n}\n0");
        var use = LevelAt(root, "Host", "Use");
        var hostBody = Body(root, "Host");

        var selection = ElaboratedScopeLookup.SelectFirstOpenLevel(use, "V");
        var provider = selection.Single!.Value.Provider;
        var opened = ElaboratedScopeLookup.LookupSingleOpenMember(use, "V")!.Value;

        Assert.Same(use, selection.Level);
        Assert.NotNull(provider.Level);
        Assert.Same(hostBody.Properties.Single(property => property.Name == "Lib"), provider.Level!.TryLookupOwnProperty("Lib")!.Value.Property);
        Assert.Same(provider.Level, opened.MemberLevel.Parent);
        Assert.Same(Body(hostBody, "Lib").Properties.Single(), opened.MemberLevel.TryLookupOwnProperty("V")!.Value.Property);
        Assert.Equal(provider.Identity, OpenProviderIdentity.DeclaredAt(provider.Target, provider.Level));
    }

    [Fact]
    public void TheRequestedStratumReachesTheProviders()
    {
        // OD-D: A's target chase returns through the carrier B, so formation keeps A as its own structure
        // (no member X), while the lower reading follows the written reference to B.
        var syntax = Parser.ParseSyntax("A = B\nB = {\n    public X = 1\n    A\n}\nU = {\n    open A\n    0\n}\n0");
        Assert.False(syntax.HasErrors);
        var operation = StaticStructureAdmission.Create(syntax.Root).Operation;
        _ = operation.CreatePreludeScope(null);
        var u = operation.LookupLevel(operation.ContextOf(operation.Root, Body(syntax.Root, "U")));
        var carrier = Body(syntax.Root, "B");

        var lower = ElaboratedScopeLookup.LookupSingleOpenMember(u, "X", StaticCycleCheck.None)!.Value;

        Assert.Same(carrier.Properties.Single(), lower.Hit.Property);
        Assert.Same(carrier.Properties.Single(), lower.MemberLevel.TryLookupOwnProperty("X")!.Value.Property);
        Assert.Same(carrier.Properties.Single(), Assert.Single(
            ElaboratedScopeLookup.LookupOpenPropertyMatches(u, "X", StaticCycleCheck.None)).Property);
        Assert.Same(u, ElaboratedScopeLookup.SelectOpenLevel(u, "X", StaticCycleCheck.None).Level);
        Assert.Null(ElaboratedScopeLookup.LookupSingleOpenMember(u, "X"));
        Assert.Empty(ElaboratedScopeLookup.LookupOpenPropertyMatches(u, "X", StaticCycleCheck.Formation));
        Assert.Equal(0, ElaboratedScopeLookup.SelectOpenLevel(u, "X").Count);
    }

    [Fact]
    public void RepeatedSelection_ReusesTheLevelsProvidersAndMemberIndexes()
    {
        var root = ValidNested("A, B", "C");
        var observations = new FrontEndTraversalObservations();
        var facts = root.CompletedStructure!.Facts;
        var prelude = ElaboratedScopeLookup.CreateScope(facts.Prelude, completedContext: facts.Context(facts.PreludeKey));
        var cache = new OpenMemberIndexCache(observations);
        var scope = ElaboratedScopeLookup.CreateScope(root, prelude, observations: observations, memberIndexes: cache);
        var outer = ElaboratedScopeLookup.CreateScope(Body(root, "Outer"), scope);
        var inner = ElaboratedScopeLookup.CreateScope(Body(Body(root, "Outer"), "Inner"), outer);

        _ = ElaboratedScopeLookup.SelectFirstOpenLevel(inner, "Missing");
        var builds = observations.LookupOpenMemberIndexBuilds;
        var reads = observations.CompletedStaticStructureReads;
        for (var repeat = 0; repeat < 100; repeat++)
        {
            Assert.Equal(1, ElaboratedScopeLookup.SelectFirstOpenLevel(inner, "Far").Count);
            Assert.Equal(0, ElaboratedScopeLookup.SelectFirstOpenLevel(inner, "Missing").Count);
        }

        Assert.Equal(builds, observations.LookupOpenMemberIndexBuilds);
        Assert.Equal(reads, observations.CompletedStaticStructureReads);
    }
}
