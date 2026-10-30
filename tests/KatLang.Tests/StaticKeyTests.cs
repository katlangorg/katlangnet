using Xunit;

namespace KatLang.Tests;

/// <summary>
/// B3-1: the static scope keys shared by the front-end passes and the static query engine
/// (<c>docs/design/static-structure-resolver-2026-10.md</c> § 9). These tests check six things:
/// <list type="bullet">
/// <item>one key per declaring chain;</item>
/// <item>the detector's levels and the resolver's declaring chains map to the same keys;</item>
/// <item>key equality is exactly <c>OpenProviderIdentity</c> equality;</item>
/// <item>one module declaration has one key wherever it is held;</item>
/// <item>a body shared by two contexts has one key per context;</item>
/// <item>written bodies keep their declaration identity through detection and resolution, a formed alias included.</item>
/// </list>
/// </summary>
public sealed class StaticKeyTests
{
    private static Algorithm.User Body(Algorithm owner, string name)
        => Assert.IsType<Algorithm.User>(owner.Properties.Single(p => p.Name == name).Value);

    private static ElaboratedPropertyScope Level(ElaboratedPropertyScope? parent, Algorithm? owner)
        => new(parent, [], [], owner: owner);

    [Fact]
    public void Inside_InternsOneKeyPerParentAndDeclaration()
    {
        var table = new StaticKeyTable();
        var a = new object();
        var b = new object();

        var first = table.Inside(table.Root, a);
        Assert.Same(first, table.Inside(table.Root, a));
        Assert.NotSame(first, table.Inside(table.Root, b));
        Assert.NotSame(first, table.Inside(first, a));
        Assert.Same(table.Root, first.Parent);
        Assert.Equal(1, first.Depth);
        Assert.Equal(2, table.Inside(first, a).Depth);
        Assert.Equal(3, table.Count);
    }

    [Fact]
    public void TheDetectorsLevels_AndTheResolversChains_NameOneKey()
    {
        var root = SourceProvenance.ParseSyntaxValidRoot("A = {\n    public B = {\n        public X = 1\n        0\n    }\n    0\n}\nM = {\n    public Y = 2\n    0\n}\n0");
        var a = Body(root, "A");
        var b = Body(a, "B");
        var module = Body(root, "M") with { IsModuleElaborated = true };
        var table = new StaticKeyTable();

        // The detector: the document root's level has no parent (the root level); nested levels own their bodies.
        var rootLevel = Level(null, root);
        var aLevel = Level(rootLevel, a);
        var bLevel = Level(aLevel, b);
        // The resolver: the document root's level is DeclaringOwners.Root; nested chains are Inside(body).
        var aOwners = DeclaringOwners.Root.Inside(a);
        var bOwners = aOwners.Inside(b);

        Assert.Same(table.Root, table.ScopeOf(rootLevel));
        Assert.Same(table.Root, table.ScopeOf(DeclaringOwners.Root));
        Assert.Same(table.ScopeOf(aLevel), table.ScopeOf(aOwners));
        Assert.Same(table.ScopeOf(bLevel), table.ScopeOf(bOwners));
        Assert.Same(table.ScopeOf(bOwners), table.BodyIn(table.BodyIn(table.Root, a), b));
        // A fresh chain object for the same path (DeclaringOwners is not interned) still names the one key.
        Assert.Same(table.ScopeOf(bOwners), table.ScopeOf(DeclaringOwners.Root.Inside(a).Inside(b)));

        // A loaded module is declared at the root level wherever it is held (Q-31 H-P, Q-32 I-U).
        var heldDeep = Level(bLevel, module);
        Assert.Same(table.Inside(table.Root, module.Declaration!), table.ScopeOf(heldDeep));
        Assert.Same(table.ScopeOf(heldDeep), table.ScopeOf(bOwners.Inside(module)));
        Assert.Same(table.ScopeOf(heldDeep), table.BodyIn(table.ScopeOf(aLevel), module));
    }

    [Fact]
    public void KeyEquality_IsProviderIdentityEquality()
    {
        // A provider declared at a level: equal OpenProviderIdentity values ⇔ one key, for every pair below.
        var root = SourceProvenance.ParseSyntaxValidRoot(
            "A = {\n    public P = { public X = 1 ⏎ 0 }\n    0\n}\nB = {\n    public Q = { public Y = 1 ⏎ 0 }\n    0\n}\n0".Replace(" ⏎ ", "\n", StringComparison.Ordinal));
        var a = Body(root, "A");
        var b = Body(root, "B");
        var p = Body(a, "P");
        var q = Body(b, "Q");
        var module = q with { IsModuleElaborated = true };
        var table = new StaticKeyTable();
        var rootLevel = Level(null, root);
        var levels = new[] { Level(rootLevel, a), Level(rootLevel, b), rootLevel };
        var providers = new Algorithm[] { p, q, module };

        foreach (var (firstProvider, firstLevel) in from provider in providers from level in levels select (provider, level))
        {
            foreach (var (secondProvider, secondLevel) in from provider in providers from level in levels select (provider, level))
            {
                var sameIdentity = OpenProviderIdentity.DeclaredAt(firstProvider, firstLevel)
                    .Equals(OpenProviderIdentity.DeclaredAt(secondProvider, secondLevel));
                var sameKey = ReferenceEquals(
                    table.BodyIn(table.ScopeOf(firstLevel), firstProvider),
                    table.BodyIn(table.ScopeOf(secondLevel), secondProvider));
                Assert.True(sameIdentity == sameKey, $"{firstProvider.Declaration} at {firstLevel.OwnerDeclaration} vs {secondProvider.Declaration} at {secondLevel.OwnerDeclaration}");
            }
        }

        // A body one host DAG shares between two levels is two scopes; the module is one, wherever it is held.
        Assert.NotSame(table.BodyIn(table.ScopeOf(levels[0]), p), table.BodyIn(table.ScopeOf(levels[1]), p));
        Assert.Same(table.BodyIn(table.ScopeOf(levels[0]), module), table.BodyIn(table.ScopeOf(levels[1]), module));
    }

    [Fact]
    public void WrittenBodies_KeepTheirDeclarationThroughDetectionAndResolution()
    {
        // Carriers, a calculation with an inferred input, and a nested body keep their written declaration: every pass
        // rewrites them with `with`. A formed alias keeps its written body's declaration too, so a body's key is one key
        // before and after alias formation; no consumer needs a provenance map.
        const string Source = "F(x) = x\nLib = {\n    public G = h + 1\n    public Inner = {\n        public V = 2\n        0\n    }\n    public R = F\n    0\n}\nLib.G(1)";
        var raw = SourceProvenance.ParseSyntaxValidRoot(Source);
        var detectedInput = ParameterDetector.DetectPrevalidated(raw);
        var (detected, detection) = detectedInput;
        Assert.Empty(detection);
        var resolved = ImplicitArgumentResolver.ResolvePrevalidated(detectedInput, new FrontEndTraversalObservations(), new DiagnosticBag());

        var rawLib = Body(raw, "Lib");
        var detectedLib = Body(detected, "Lib");
        var resolvedLib = Body(resolved, "Lib");
        Assert.Same(raw.Declaration, detected.Declaration);
        Assert.Same(raw.Declaration, resolved.Declaration);
        Assert.Same(rawLib.Declaration, detectedLib.Declaration);
        Assert.Same(rawLib.Declaration, resolvedLib.Declaration);
        foreach (var name in new[] { "G", "Inner" })
        {
            Assert.Same(Body(rawLib, name).Declaration, Body(detectedLib, name).Declaration);
            Assert.Same(Body(rawLib, name).Declaration, Body(resolvedLib, name).Declaration);
        }

        Assert.Equal(new[] { "h" }, Body(resolvedLib, "G").Params);
        var alias = Assert.IsType<Algorithm.Alias>(resolvedLib.Properties.Single(p => p.Name == "R").Value);
        Assert.Same(Body(rawLib, "R").Declaration, alias.Declaration);
    }

    [Fact]
    public void QueryKeys_CompareScopesAndNodesByReference()
    {
        var table = new StaticKeyTable();
        var scope = table.Inside(table.Root, new object());
        var other = table.Inside(table.Root, new object());
        var edge = new Expr.DotCall(new Expr.Resolve("a"), "b", null);
        var equalEdge = new Expr.DotCall(new Expr.Resolve("a"), "b", null);
        Assert.Equal(edge, equalEdge);

        Assert.Equal(StaticQueryKey.MissSelection(scope, edge), StaticQueryKey.MissSelection(scope, edge));
        Assert.NotEqual(StaticQueryKey.MissSelection(scope, edge), StaticQueryKey.MissSelection(scope, equalEdge));
        Assert.NotEqual(StaticQueryKey.IsInput(scope, "x"), StaticQueryKey.IsInput(other, "x"));
        Assert.NotEqual(StaticQueryKey.IsInput(scope, "x"), StaticQueryKey.IsInput(scope, "X"));
        Assert.Equal(StaticQueryKey.Binding(scope, "x", StaticCycleCheck.Formation), StaticQueryKey.Binding(scope, "x", StaticCycleCheck.Formation));
        Assert.NotEqual(StaticQueryKey.Binding(scope, "x", StaticCycleCheck.Formation), StaticQueryKey.Binding(scope, "x", StaticCycleCheck.Lower));
        Assert.NotEqual(StaticQueryKey.Inputs(scope), StaticQueryKey.Members(scope));
        Assert.Equal(StaticQueryKey.IsInput(scope, "x").GetHashCode(), StaticQueryKey.IsInput(scope, "x").GetHashCode());

        // One engine holds every family: a key is a usable engine key.
        var engine = new StaticQueryEngine<StaticQueryKey, int>(new ConstantDefinition());
        Assert.Equal(1, engine.Get(StaticQueryKey.Inputs(scope)));
        Assert.Equal(1, engine.Statistics.Entries);
    }

    private sealed class ConstantDefinition : IStaticQueryDefinition<StaticQueryKey, int>
    {
        public StaticQueryStep<int> Compute(StaticQueryKey key, StaticQueryReader<StaticQueryKey, int> reader) => StaticQueryStep.Complete(1);

        public int Initial(StaticQueryKey key) => 0;

        public int PathCycleValue => -1;

        public bool ValueEquals(int left, int right) => left == right;

        public bool IsRefinement(int before, int after) => before == 0 || before == after;
    }
}
