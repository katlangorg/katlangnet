using System.Text;
using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// M18 regressions for the <see cref="ElaboratedScopeLookup"/> acceleration
/// caches: the per-level lazy property-name index, the per-level resolved
/// <c>open</c>-provider cache, and the per-chain cached root.
///
/// <para>Two families of guarantees are pinned here. SEMANTIC: every cached
/// answer must be exactly what the authoritative linear relation over the
/// ordered declaration lists selects — first occurrence wins by declaration
/// IDENTITY, ordinal name comparison, ownership-first level order, open dedup
/// and same-level ambiguity, and per-operation cache lifetime (a host mutating
/// its AST between operations is observed by the next operation). A test-local
/// linear oracle (not the production helpers) supplies the reference relation.
/// STRUCTURAL: deterministic work counters prove the wide-scope lookup work is
/// index construction plus index probes — not repeated linear scans, repeated
/// open-target resolution, or repeated root walks.</para>
/// </summary>
public class ElaboratedLookupAccelerationTests
{
    // ── scenario sources (mirrors FrontEndElaborationScenarios in the benchmarks project) ──

    private static string BuildWideLookupChainSource(int count)
    {
        var source = new StringBuilder();
        source.AppendLine("V0 = 1");
        for (var i = 1; i < count; i++)
            source.AppendLine($"V{i} = V{i - 1} + 1");
        source.AppendLine($"V{count - 1}");
        return source.ToString();
    }

    private static string BuildWideLookupMissSource(int count)
    {
        var source = new StringBuilder();
        for (var i = 0; i < count; i++)
            source.AppendLine($"V{i} = {i}");
        for (var i = 0; i < count; i++)
            source.AppendLine($"u{i}");
        return source.ToString();
    }

    private static string BuildNestedChainSource(int depth)
    {
        var source = new StringBuilder();
        for (var level = 0; level < depth; level++)
        {
            source.AppendLine($"L{level}(x{level}) = {{");
            source.AppendLine($"A{level} = x{level} + 1");
            source.AppendLine($"B{level} = A{level} + 1");
        }

        source.AppendLine("1");
        for (var level = depth - 1; level >= 0; level--)
        {
            source.AppendLine($"B{level}");
            source.AppendLine("}");
        }

        source.AppendLine("L0(1)");
        return source.ToString();
    }

    private const string OpenHeavySource = """
        Lib = {
            public A = 1
            public B = 2
            public C = 3
        }
        Use = {
            open Lib
            A + B + C + A + B + C
        }
        Use
        """;

    private static FrontEndTraversalObservations MeasureDetection(string source)
    {
        var syntax = Parser.ParseSyntax(source);
        Assert.False(syntax.HasErrors);
        var observations = new FrontEndTraversalObservations();
        var (_, diagnostics) = ParameterDetector.DetectPrevalidated(syntax.Root, null, observations);
        Assert.DoesNotContain(diagnostics, d => d.Severity == DiagnosticSeverity.Error);
        return observations;
    }

    // ── structural work-count regressions ────────────────────────────────────

    /// <summary>
    /// The wide flat calculation chain resolves every reference at the root
    /// level. Accelerated lookup performs NO linear property-name scans and
    /// builds exactly ONE index (the root level; body levels are empty and the
    /// prelude is never reached) — at every width, so total lookup work is the
    /// one O(P) index construction plus O(P) probes, not O(P²) scanning.
    /// </summary>
    [Theory]
    [InlineData(100, 199)]
    [InlineData(200, 399)]
    [InlineData(400, 799)]
    [InlineData(800, 1599)]
    public void WideChainLookupBuildsOneIndexAndScansNothing(int width, long expectedLevelVisits)
    {
        var observations = MeasureDetection(BuildWideLookupChainSource(width));

        Assert.Equal(0, observations.LookupPropertyComparisons);
        Assert.Equal(1, observations.LookupNameIndexBuilds);
        Assert.Equal(expectedLevelVisits, observations.LookupLevelVisits);
        Assert.Equal(0, observations.LookupOpenTargetResolutions);
        Assert.Equal(0, observations.LookupOpenMemberIndexBuilds);
        Assert.Equal(0, observations.LookupRootDiscoveryWalks);
    }

    /// <summary>
    /// The miss-heavy workload walks the full chain (root and prelude) for
    /// every promoted implicit parameter, and the near-miss suggestion
    /// machinery re-queries the chain per gathered candidate. All of it is
    /// index-served: exactly two indexes exist (root level and prelude level),
    /// each built once, with zero linear scans.
    /// </summary>
    [Theory]
    [InlineData(100)]
    [InlineData(200)]
    [InlineData(400)]
    [InlineData(800)]
    public void WideMissLookupBuildsEachQueriedLevelIndexOnce(int width)
    {
        var observations = MeasureDetection(BuildWideLookupMissSource(width));

        Assert.Equal(0, observations.LookupPropertyComparisons);
        Assert.Equal(2, observations.LookupNameIndexBuilds);
        Assert.True(observations.LookupLevelVisits > 0);
        Assert.Equal(0, observations.LookupOpenTargetResolutions);
        Assert.Equal(0, observations.LookupRootDiscoveryWalks);
    }

    /// <summary>
    /// A consulted level resolves each of its open targets ONCE per operation
    /// (six opened-name lookups previously re-resolved the target six times),
    /// builds the provider's exported-member index once, and never walks to
    /// the chain root (the root is captured at construction).
    /// </summary>
    [Fact]
    public void OpenTargetsResolveOncePerConsultedLevel()
    {
        var observations = MeasureDetection(OpenHeavySource);

        Assert.Equal(1, observations.LookupOpenTargetResolutions);
        Assert.Equal(1, observations.LookupOpenMemberIndexBuilds);
        Assert.Equal(0, observations.LookupPropertyComparisons);
        Assert.Equal(2, observations.LookupNameIndexBuilds);
        Assert.Equal(0, observations.LookupRootDiscoveryWalks);
    }

    /// <summary>
    /// Open-target resolution stays LAZY: a level whose opens are never
    /// consulted (every queried name resolves directly) resolves no target and
    /// builds no provider state, exactly like the pre-cache code. This also
    /// pins the error/side-effect ordering argument: nothing about a level's
    /// opens runs earlier than it did before the cache.
    /// </summary>
    [Fact]
    public void UnconsultedOpensResolveNothing()
    {
        const string source = """
            Lib = {
                public A = 1
            }
            Use = {
                open Lib
                B = 2
                B + B
            }
            Use
            """;
        var observations = MeasureDetection(source);

        Assert.Equal(0, observations.LookupOpenTargetResolutions);
        Assert.Equal(0, observations.LookupOpenMemberIndexBuilds);
    }

    /// <summary>
    /// The direct phase searches the ENTIRE ownership chain before any open is
    /// consulted. A parent declaration therefore suppresses even ambiguous
    /// child opens, and their provider cache remains cold.
    /// </summary>
    [Fact]
    public void ParentDirectHitSuppressesAmbiguousChildOpens()
    {
        var parentX = new Property("X", ValueAlgorithm(303));
        var libA = Owner(new Property("X", ValueAlgorithm(101), IsPublic: true));
        var libB = Owner(new Property("X", ValueAlgorithm(202), IsPublic: true));
        var observations = new FrontEndTraversalObservations();
        var rootScope = ElaboratedScopeLookup.CreateScope(Owner(
            parentX,
            new Property("LibA", libA),
            new Property("LibB", libB)), observations: observations);
        var childScope = ElaboratedScopeLookup.CreateScope(
            new Algorithm.User(
                null,
                [],
                [new Expr.Resolve("LibA"), new Expr.Resolve("LibB")],
                [],
                OutputBundle.Empty),
            rootScope);

        var hit = Assert.Single(ElaboratedScopeLookup.LookupLexicalPropertyMatches(childScope, "X"));
        Assert.Same(parentX, hit.Property);
        Assert.Equal(0, observations.LookupOpenTargetResolutions);
        Assert.Equal(0, observations.LookupOpenMemberIndexBuilds);
    }

    /// <summary>
    /// Deep nested chain: every queried non-empty level (root, each of the
    /// depth nested algorithm levels, and the prelude — reached by the
    /// captured-parameter shadow misses) builds its index at most once.
    /// </summary>
    [Fact]
    public void NestedChainBuildsEachQueriedLevelIndexOnce()
    {
        const int depth = 8;
        var observations = MeasureDetection(BuildNestedChainSource(depth));

        Assert.Equal(depth + 2, observations.LookupNameIndexBuilds);
        Assert.Equal(0, observations.LookupPropertyComparisons);
        Assert.Equal(0, observations.LookupRootDiscoveryWalks);
    }

    /// <summary>
    /// Two independent detections of the same source observe identical,
    /// complete work: the second operation builds its own indexes again
    /// because nothing is cached globally or across operations.
    /// </summary>
    [Fact]
    public void IndependentDetectionsShareNoCacheState()
    {
        var source = BuildWideLookupChainSource(50);
        var first = MeasureDetection(source);
        var second = MeasureDetection(source);

        Assert.Equal(1, first.LookupNameIndexBuilds);
        Assert.Equal(1, second.LookupNameIndexBuilds);
        Assert.Equal(first.LookupLevelVisits, second.LookupLevelVisits);
        Assert.Equal(first.LookupPropertyComparisons, second.LookupPropertyComparisons);
    }

    // ── declaration-identity regressions ─────────────────────────────────────

    private static Algorithm.User ValueAlgorithm(int sentinel)
        => new(null, [], [], [], [new Expr.Num(sentinel)]);

    private static Algorithm.User Owner(params Property[] properties)
        => new(null, [], [], [.. properties], OutputBundle.Empty);

    /// <summary>
    /// Duplicate same-name declarations in ONE level resolve to the FIRST list
    /// entry by reference identity — the index must never let a later
    /// same-name declaration (host-built trees can contain them) win.
    /// </summary>
    [Fact]
    public void DuplicateNamesResolveToFirstDeclarationByIdentity()
    {
        var firstX = new Property("X", ValueAlgorithm(101));
        var laterX = new Property("X", ValueAlgorithm(202));
        var owner = Owner(
            new Property("A", ValueAlgorithm(1)),
            firstX,
            new Property("B", ValueAlgorithm(2)),
            new Property("C", ValueAlgorithm(3)),
            new Property("D", ValueAlgorithm(4)),
            new Property("E", ValueAlgorithm(5)),
            new Property("F", ValueAlgorithm(6)),
            laterX);
        var scope = ElaboratedScopeLookup.CreateScope(owner);

        // Twice: the first query builds the index, the second is served by it.
        for (var round = 0; round < 2; round++)
        {
            var hit = ElaboratedScopeLookup.TryLookupDirectLexicalProperty(scope, "X");
            Assert.NotNull(hit);
            Assert.Same(firstX, hit.Value.Property);
            Assert.Same(owner, hit.Value.Owner);

            var matches = ElaboratedScopeLookup.LookupLexicalPropertyMatches(scope, "X");
            var match = Assert.Single(matches);
            Assert.Same(firstX, match.Property);
        }
    }

    /// <summary>
    /// The opened-member lookup rule is first-QUALIFYING-occurrence: a
    /// non-public same-name entry earlier in the provider's list is skipped
    /// and a later public exported entry is the answer — exactly the linear
    /// <see cref="ElaboratedScopeLookup.TryLookupPublicExportedProperty"/>
    /// relation, which the provider's member index must replicate.
    /// </summary>
    [Fact]
    public void OpenedMemberLookupSkipsNonQualifyingDuplicates()
    {
        var privateX = new Property("X", ValueAlgorithm(101));
        var publicX = new Property("X", ValueAlgorithm(202), IsPublic: true);
        var lib = Owner(privateX, publicX);
        var root = Owner(new Property("Lib", lib, IsPublic: true));
        var user = new Algorithm.User(null, [], [new Expr.Resolve("Lib")], [], OutputBundle.Empty);

        var rootScope = ElaboratedScopeLookup.CreateScope(root);
        var userScope = ElaboratedScopeLookup.CreateScope(user, rootScope);

        // The linear helper defines the relation…
        var linear = ElaboratedScopeLookup.TryLookupPublicExportedProperty(lib, "X");
        Assert.NotNull(linear);
        Assert.Same(publicX, linear.Value.Property);

        // …and the cached opened-name path must select the same declaration.
        for (var round = 0; round < 2; round++)
        {
            var hits = ElaboratedScopeLookup.LookupOpenPropertyMatches(userScope, "X");
            var hit = Assert.Single(hits);
            Assert.Same(publicX, hit.Property);
            Assert.Same(lib, hit.Owner);
        }
    }

    /// <summary>Identifier lookup stays exactly case-sensitive (ordinal).</summary>
    [Fact]
    public void LookupIsCaseSensitive()
    {
        var lower = new Property("value", ValueAlgorithm(101));
        var upper = new Property("Value", ValueAlgorithm(202));
        var scope = ElaboratedScopeLookup.CreateScope(Owner(lower, upper));

        Assert.Same(lower, ElaboratedScopeLookup.TryLookupDirectLexicalProperty(scope, "value")!.Value.Property);
        Assert.Same(upper, ElaboratedScopeLookup.TryLookupDirectLexicalProperty(scope, "Value")!.Value.Property);
        Assert.Null(ElaboratedScopeLookup.TryLookupDirectLexicalProperty(scope, "VALUE"));
        Assert.Null(ElaboratedScopeLookup.TryLookupDirectLexicalProperty(scope, "vAlue"));
    }

    /// <summary>Ordinal lookup preserves Unicode code-point-sequence identity without normalization.</summary>
    [Fact]
    public void LookupUsesOrdinalUnicodeIdentity()
    {
        const string composed = "é";
        const string decomposed = "e\u0301";
        var pi = new Property("π", ValueAlgorithm(101));
        var composedProperty = new Property(composed, ValueAlgorithm(202));
        var decomposedProperty = new Property(decomposed, ValueAlgorithm(303));
        var scope = ElaboratedScopeLookup.CreateScope(Owner(pi, composedProperty, decomposedProperty));

        Assert.Same(pi, ElaboratedScopeLookup.TryLookupDirectLexicalProperty(scope, "π")!.Value.Property);
        Assert.Same(composedProperty, ElaboratedScopeLookup.TryLookupDirectLexicalProperty(scope, composed)!.Value.Property);
        Assert.Same(decomposedProperty, ElaboratedScopeLookup.TryLookupDirectLexicalProperty(scope, decomposed)!.Value.Property);
    }

    /// <summary>
    /// A malformed host property with a null name was tolerated by the old
    /// ordinal scan: valid queries skipped it, and a malformed null query
    /// selected it first-occurrence-wins. The index preserves both behaviors
    /// without trying to insert or probe a null dictionary key.
    /// </summary>
    [Fact]
    public void NullHostPropertyNameDoesNotPoisonValidLookup()
    {
        var firstNull = new Property(null!, ValueAlgorithm(101));
        var valid = new Property("Valid", ValueAlgorithm(202));
        var scope = ElaboratedScopeLookup.CreateScope(Owner(
            firstNull,
            valid,
            new Property(null!, ValueAlgorithm(303))));

        for (var round = 0; round < 2; round++)
        {
            Assert.Same(valid, ElaboratedScopeLookup.TryLookupDirectLexicalProperty(scope, "Valid")!.Value.Property);
            Assert.Same(firstNull, ElaboratedScopeLookup.TryLookupDirectLexicalProperty(scope, null!)!.Value.Property);
        }
    }

    /// <summary>The opened-member index preserves the same malformed null-name tolerance.</summary>
    [Fact]
    public void NullOpenedMemberNameRetainsFirstQualifyingIdentity()
    {
        var firstNull = new Property(null!, ValueAlgorithm(101), IsPublic: true);
        var lib = Owner(
            new Property(null!, ValueAlgorithm(99)),
            firstNull,
            new Property(null!, ValueAlgorithm(303), IsPublic: true));
        var rootScope = ElaboratedScopeLookup.CreateScope(Owner(new Property("Lib", lib)));
        var userScope = ElaboratedScopeLookup.CreateScope(
            new Algorithm.User(null, [], [new Expr.Resolve("Lib")], [], OutputBundle.Empty),
            rootScope);

        for (var round = 0; round < 2; round++)
        {
            var hit = Assert.Single(ElaboratedScopeLookup.LookupOpenPropertyMatches(userScope, null!));
            Assert.Same(firstNull, hit.Property);
        }
    }

    /// <summary>
    /// Ownership-first shadowing across levels: the NEAREST level's
    /// declaration wins by identity, and each level's index answers only for
    /// its own level.
    /// </summary>
    [Fact]
    public void NearestLevelDeclarationWinsAcrossLevels()
    {
        var rootX = new Property("X", ValueAlgorithm(101));
        var childX = new Property("X", ValueAlgorithm(202));
        var rootOnly = new Property("RootOnly", ValueAlgorithm(303));
        var rootScope = ElaboratedScopeLookup.CreateScope(Owner(rootX, rootOnly));
        var childScope = ElaboratedScopeLookup.CreateScope(Owner(childX), rootScope);
        var grandchildScope = ElaboratedScopeLookup.CreateScope(Owner(), childScope);

        Assert.Same(childX, ElaboratedScopeLookup.TryLookupDirectLexicalProperty(grandchildScope, "X")!.Value.Property);
        Assert.Same(rootOnly, ElaboratedScopeLookup.TryLookupDirectLexicalProperty(grandchildScope, "RootOnly")!.Value.Property);
        Assert.Same(rootX, ElaboratedScopeLookup.TryLookupDirectLexicalProperty(rootScope, "X")!.Value.Property);
    }

    // ── linear-oracle differential ───────────────────────────────────────────
    // A deliberately simple test-local reference implementation of the
    // documented lookup relation, sharing NO code with the production caches.

    private static PropertyLookupHit? OracleDirect(ElaboratedPropertyScope scope, string name)
    {
        for (var current = scope; current is not null; current = current.Parent)
        {
            foreach (var hit in current.Properties)
            {
                if (string.Equals(hit.Property.Name, name, StringComparison.Ordinal))
                    return hit;
            }
        }

        return null;
    }

    private static Property? OracleFirstQualifying(Algorithm owner, string name)
    {
        foreach (var property in owner.Properties)
        {
            if (string.Equals(property.Name, name, StringComparison.Ordinal)
                && property.IsPublic
                && property.Exposure == PropertyExposure.Exported)
            {
                return property;
            }
        }

        return null;
    }

    private static Algorithm? OracleResolveOpenTarget(ElaboratedPropertyScope scope, Expr openExpr) => openExpr switch
    {
        Expr.Resolve(var name) => OracleDirect(scope, name)?.Property.Value,
        Expr.DotCall { Args: null } dot => OracleResolveOpenTarget(scope, dot.Target) is { } target
            ? OracleFirstQualifying(target, dot.Name)?.Value
            : null,
        Expr.AlgorithmExpr(var algorithm) => algorithm,
        _ => throw new InvalidOperationException("The oracle differential only constructs resolve/dotted/inline open targets."),
    };

    private static string OracleDedupKey(Expr openExpr, int index) => openExpr switch
    {
        Expr.Resolve(var name) => name,
        Expr.DotCall { Args: null } dot => OracleDedupKey(dot.Target, index) + "." + dot.Name,
        Expr.AlgorithmExpr => $"(inline#{index})",
        _ => throw new InvalidOperationException("The oracle differential only constructs resolve/dotted/inline open targets."),
    };

    private static List<PropertyLookupHit> OracleOpenMatches(ElaboratedPropertyScope scope, string name)
    {
        for (var current = scope; current is not null; current = current.Parent)
        {
            var hits = new List<PropertyLookupHit>();
            var seenKeys = new HashSet<string>(StringComparer.Ordinal);
            for (var i = 0; i < current.Opens.Count; i++)
            {
                if (!seenKeys.Add(OracleDedupKey(current.Opens[i], i)))
                    continue;

                var target = OracleResolveOpenTarget(current, current.Opens[i]);
                if (target is null)
                    continue;

                if (OracleFirstQualifying(target, name) is { } property)
                    hits.Add(new PropertyLookupHit(target, property));
            }

            if (hits.Count > 0)
                return hits;
        }

        return [];
    }

    /// <summary>
    /// Differential over a scope battery combining wide levels, in-level
    /// duplicates, cross-level shadowing, duplicate and unresolvable open
    /// targets, dotted targets, same-level provider ambiguity, and
    /// case-sensitive near-collisions: for every declared and missing probe
    /// name, the accelerated lookups select exactly the declarations the
    /// linear oracle selects, by reference identity — on a cold chain and
    /// again on the warm one.
    /// </summary>
    [Fact]
    public void AcceleratedLookupMatchesLinearOracleByIdentity()
    {
        var libA = Owner(
            new Property("Opened", ValueAlgorithm(11), IsPublic: true),
            new Property("UniqueA", ValueAlgorithm(12), IsPublic: true),
            new Property("NotPublic", ValueAlgorithm(13)),
            new Property("caseSense", ValueAlgorithm(14), IsPublic: true));
        var libB = Owner(
            new Property("Dup", ValueAlgorithm(21)),
            new Property("Dup", ValueAlgorithm(22), IsPublic: true),
            new Property("Opened", ValueAlgorithm(23), IsPublic: true));
        var inner = Owner(new Property("Deep", ValueAlgorithm(31), IsPublic: true));
        var outer = Owner(new Property("Inner", inner, IsPublic: true));

        var rootProperties = new List<Property>();
        for (var i = 0; i < 40; i++)
            rootProperties.Add(new Property($"R{i}", ValueAlgorithm(100 + i)));
        rootProperties.Add(new Property("Twice", ValueAlgorithm(41)));
        rootProperties.Add(new Property("Shadow", ValueAlgorithm(42)));
        rootProperties.Add(new Property("LibA", libA, IsPublic: true));
        rootProperties.Add(new Property("LibB", libB, IsPublic: true));
        rootProperties.Add(new Property("Outer", outer, IsPublic: true));
        rootProperties.Add(new Property("Twice", ValueAlgorithm(43)));
        var root = new Algorithm.User(null, [], [], rootProperties, OutputBundle.Empty);

        var mid = new Algorithm.User(
            null,
            [],
            Opens:
            [
                new Expr.Resolve("LibA"),
                new Expr.Resolve("LibB"),
                new Expr.Resolve("LibA"), // duplicate spelling: one provider
                new Expr.Resolve("Missing"), // unresolvable target
                new Expr.DotCall(new Expr.Resolve("Outer"), "Inner"),
            ],
            Properties: [new Property("Shadow", ValueAlgorithm(51)), new Property("MidOnly", ValueAlgorithm(52))],
            Output: OutputBundle.Empty);
        var leaf = Owner(new Property("LeafOnly", ValueAlgorithm(61)));

        var rootScope = ElaboratedScopeLookup.CreateScope(root);
        var midScope = ElaboratedScopeLookup.CreateScope(mid, rootScope);
        var leafScope = ElaboratedScopeLookup.CreateScope(leaf, midScope);

        var probes = new List<string>
        {
            "R0", "R20", "R39", "Twice", "Shadow", "MidOnly", "LeafOnly",
            "LibA", "LibB", "Outer",
            "Opened", "UniqueA", "NotPublic", "Dup", "Deep",
            "caseSense", "CaseSense", "casesense",
            "Missing", "zzAbsent", "r0", "twice",
        };

        // Two rounds: cold caches, then warm caches — identical selections.
        for (var round = 0; round < 2; round++)
        {
            foreach (var scope in new[] { leafScope, midScope, rootScope })
            {
                foreach (var name in probes)
                {
                    var expectedDirect = OracleDirect(scope, name);
                    var actualDirect = ElaboratedScopeLookup.TryLookupDirectLexicalProperty(scope, name);
                    AssertSameHit(expectedDirect, actualDirect, name);

                    var expectedOpen = OracleOpenMatches(scope, name);
                    var actualOpen = ElaboratedScopeLookup.LookupOpenPropertyMatches(scope, name);
                    Assert.Equal(expectedOpen.Count, actualOpen.Count);
                    for (var i = 0; i < expectedOpen.Count; i++)
                        AssertSameHit(expectedOpen[i], actualOpen[i], name);

                    var expectedLexical = expectedDirect is { } direct
                        ? [direct]
                        : expectedOpen;
                    var actualLexical = ElaboratedScopeLookup.LookupLexicalPropertyMatches(scope, name);
                    Assert.Equal(expectedLexical.Count, actualLexical.Count);
                    for (var i = 0; i < expectedLexical.Count; i++)
                        AssertSameHit(expectedLexical[i], actualLexical[i], name);
                }
            }
        }

        // The battery must actually exercise the interesting shapes.
        Assert.Equal(2, ElaboratedScopeLookup.LookupOpenPropertyMatches(leafScope, "Opened").Count); // same-level ambiguity
        Assert.Single(ElaboratedScopeLookup.LookupOpenPropertyMatches(leafScope, "Dup")); // in-provider qualifying duplicate
        Assert.Single(ElaboratedScopeLookup.LookupOpenPropertyMatches(leafScope, "Deep")); // dotted provider
        Assert.Empty(ElaboratedScopeLookup.LookupOpenPropertyMatches(leafScope, "NotPublic")); // private is not provided
    }

    private static void AssertSameHit(PropertyLookupHit? expected, PropertyLookupHit? actual, string name)
    {
        if (expected is null)
        {
            Assert.True(actual is null, $"'{name}': oracle resolved nothing but accelerated lookup resolved a declaration.");
            return;
        }

        Assert.True(actual is not null, $"'{name}': oracle resolved a declaration but accelerated lookup resolved nothing.");
        Assert.Same(expected.Value.Property, actual!.Value.Property);
        Assert.Same(expected.Value.Owner, actual.Value.Owner);
    }

    // ── provider cache shape ─────────────────────────────────────────────────

    /// <summary>
    /// Resolved providers preserve open DECLARATION order, deduplicate named
    /// targets first-occurrence-wins, and cache the exact target algorithm
    /// identity per level — never a text-keyed or reconstructed target.
    /// </summary>
    [Fact]
    public void ResolvedOpenProvidersPreserveOrderDedupAndIdentity()
    {
        var libA = Owner(new Property("A", ValueAlgorithm(1), IsPublic: true));
        var libB = Owner(new Property("B", ValueAlgorithm(2), IsPublic: true));
        var root = Owner(
            new Property("LibA", libA, IsPublic: true),
            new Property("LibB", libB, IsPublic: true));
        var user = new Algorithm.User(
            null,
            [],
            Opens: [new Expr.Resolve("LibB"), new Expr.Resolve("LibA"), new Expr.Resolve("LibB")],
            Properties: [],
            Output: OutputBundle.Empty);

        var rootScope = ElaboratedScopeLookup.CreateScope(root);
        var userScope = ElaboratedScopeLookup.CreateScope(user, rootScope);

        var providers = userScope.GetResolvedOpenProviders();
        Assert.Equal(2, providers.Count);
        Assert.Same(libB, providers[0].Target);
        Assert.Same(libA, providers[1].Target);
        Assert.Same(providers, userScope.GetResolvedOpenProviders());
    }

    /// <summary>
    /// The SAME open spelling in two scopes resolves per scope: each level's
    /// provider cache holds the target ITS ownership-first resolution selects,
    /// so a nearer same-named library shadows the outer one. Pins that no
    /// cache is keyed by target text across contexts, front-end and runtime
    /// agreeing on the selected declarations.
    /// </summary>
    [Fact]
    public void SameSpelledOpenTargetResolvesPerScope()
    {
        const string source = """
            Lib = {
                public X = 101
            }
            A = {
                open Lib
                X
            }
            B = {
                open Lib
                Lib = {
                    public X = 202
                }
                X
            }
            A + B
            """;
        Assert.Equal("ok raw=303 n=1", SemanticExplorerHarness.Observe("m18.sameSpelledOpens", source).Neutral);

        var parsed = SourceProvenance.ParseValid(source);
        var root = Assert.IsType<Algorithm.User>(parsed.Root);
        var outerLib = root.Properties.Single(p => p.Name == "Lib").Value;
        var a = root.Properties.Single(p => p.Name == "A").Value;
        var b = Assert.IsType<Algorithm.User>(root.Properties.Single(p => p.Name == "B").Value);
        var innerLib = b.Properties.Single(p => p.Name == "Lib").Value;

        var rootScope = ElaboratedScopeLookup.CreateScope(parsed.Root);
        var aProviders = ElaboratedScopeLookup.CreateScope(a, rootScope).GetResolvedOpenProviders();
        var bProviders = ElaboratedScopeLookup.CreateScope(b, rootScope).GetResolvedOpenProviders();

        Assert.Same(outerLib, Assert.Single(aProviders).Target);
        Assert.Same(innerLib, Assert.Single(bProviders).Target);
    }

    // ── prelude-shadow decisions on the cached chain root ────────────────────

    /// <summary>
    /// A captured ancestor parameter sharing a PRELUDE property's name stays
    /// the parameter (the prelude root is always farther than the capturing
    /// algorithm), while a NON-prelude ancestor property with that name
    /// shadows the captured parameter. The decision anchors on the chain's
    /// cached root; both directions are pinned structurally (Param vs Resolve
    /// in the elaborated AST) and at runtime.
    /// </summary>
    [Fact]
    public void CapturedParameterShadowDecisionsAnchorOnChainRoot()
    {
        const string preludeCollision = """
            Outer(count) = {
                Inner = {
                    count
                }
                Inner
            }
            Outer(707)
            """;
        Assert.Equal("ok raw=707 n=1", SemanticExplorerHarness.Observe("m18.preludeShadow", preludeCollision).Neutral);
        var preludeRoot = Assert.IsType<Algorithm.User>(SourceProvenance.ParseValid(preludeCollision).Root);
        var innerBody = InnerOf(preludeRoot);
        Assert.IsType<Expr.Param>(innerBody.Output[0]);

        const string ancestorShadow = """
            value = 505
            Outer(value) = {
                Inner = {
                    value
                }
                Inner
            }
            Outer(707)
            """;
        Assert.Equal("ok raw=505 n=1", SemanticExplorerHarness.Observe("m18.ancestorShadow", ancestorShadow).Neutral);
        var shadowRoot = Assert.IsType<Algorithm.User>(SourceProvenance.ParseValid(ancestorShadow).Root);
        Assert.IsType<Expr.Resolve>(InnerOf(shadowRoot).Output[0]);

        // The direct-hit shadow decision reads the cached chain root — no
        // per-decision parent walk happens even on this hit-branch workload.
        Assert.Equal(0, MeasureDetection(ancestorShadow).LookupRootDiscoveryWalks);

        static Algorithm.User InnerOf(Algorithm.User root)
        {
            var outer = Assert.IsType<Algorithm.User>(root.Properties.Single(p => p.Name == "Outer").Value);
            return Assert.IsType<Algorithm.User>(outer.Properties.Single(p => p.Name == "Inner").Value);
        }
    }

    /// <summary>
    /// Consecutive independent detections each anchor shadow decisions on
    /// THEIR OWN chain root: the second run of the prelude-collision program
    /// classifies identically (a root cached beyond one operation would
    /// compare against a stale prelude instance and flip the decision).
    /// </summary>
    [Fact]
    public void ConsecutiveDetectionsAnchorOnTheirOwnRoot()
    {
        const string source = """
            Outer(count) = {
                Inner = {
                    count
                }
                Inner
            }
            Outer(707)
            """;
        for (var run = 0; run < 2; run++)
        {
            var root = Assert.IsType<Algorithm.User>(SourceProvenance.ParseValid(source).Root);
            var outer = Assert.IsType<Algorithm.User>(root.Properties.Single(p => p.Name == "Outer").Value);
            var inner = Assert.IsType<Algorithm.User>(outer.Properties.Single(p => p.Name == "Inner").Value);
            Assert.IsType<Expr.Param>(inner.Output[0]);
        }
    }

    /// <summary>
    /// An open-provided hit is non-prelude visibility and therefore shadows a
    /// captured ancestor parameter, even though no direct declaration does.
    /// </summary>
    [Fact]
    public void OpenHitShadowsCapturedAncestorParameter()
    {
        const string source = """
            Lib = {
                public x = 101
            }
            Outer(x) = {
                Inner = {
                    open Lib
                    x
                }
                Inner
            }
            Outer(707)
            """;

        Assert.Equal("ok raw=101 n=1", SemanticExplorerHarness.Observe("m18.openCapturedShadow", source).Neutral);
        var root = Assert.IsType<Algorithm.User>(SourceProvenance.ParseValid(source).Root);
        var outer = Assert.IsType<Algorithm.User>(root.Properties.Single(p => p.Name == "Outer").Value);
        var inner = Assert.IsType<Algorithm.User>(outer.Properties.Single(p => p.Name == "Inner").Value);
        Assert.IsType<Expr.Resolve>(inner.Output[0]);
    }

    /// <summary>
    /// Root identity is derived from each chain, never from equivalent content,
    /// an immediate parent, or a process-global slot.
    /// </summary>
    [Fact]
    public void IndependentChainsKeepTheirExactRootIdentity()
    {
        var firstRoot = ElaboratedScopeLookup.CreateScope(Owner(new Property("R", ValueAlgorithm(101))));
        var firstMiddle = ElaboratedScopeLookup.CreateScope(Owner(), firstRoot);
        var firstLeaf = ElaboratedScopeLookup.CreateScope(Owner(), firstMiddle);
        var secondRoot = ElaboratedScopeLookup.CreateScope(Owner(new Property("R", ValueAlgorithm(202))));
        var secondLeaf = ElaboratedScopeLookup.CreateScope(Owner(), secondRoot);

        Assert.Same(firstRoot, firstLeaf.Root);
        Assert.NotSame(firstMiddle, firstLeaf.Root);
        Assert.Same(secondRoot, secondLeaf.Root);
        Assert.NotSame(firstLeaf.Root, secondLeaf.Root);
    }

    // ── per-operation cache lifetime under host mutation ─────────────────────

    /// <summary>
    /// A host that mutates its own (caller-owned) property list BETWEEN
    /// elaboration operations is observed by the next operation: each
    /// operation snapshots and indexes fresh state, so no cache carries over.
    /// </summary>
    [Fact]
    public void HostMutationBetweenOperationsIsObserved()
    {
        var properties = new List<Property> { new("Target", ValueAlgorithm(101)) };
        var root = new Algorithm.User(null, [], [], properties, [new Expr.Resolve("Target")]);

        var (first, firstDiagnostics) = ParameterDetector.Detect(root);
        Assert.DoesNotContain(firstDiagnostics, d => d.Severity == DiagnosticSeverity.Error);
        Assert.Empty(first.Parameters);

        properties.RemoveAt(0);

        var (second, secondDiagnostics) = ParameterDetector.Detect(root);
        Assert.DoesNotContain(secondDiagnostics, d => d.Severity == DiagnosticSeverity.Error);
        var promoted = Assert.Single(second.Parameters);
        Assert.Equal("Target", promoted.Name);
    }

    /// <summary>
    /// The same per-operation lifetime holds for scopes created over ORIGINAL
    /// (un-rewritten) nodes — a conditional branch body's scope is created from
    /// the host's own algorithm object, so a scope cached beyond one operation
    /// would keep serving the stale property snapshot. The second detection
    /// must observe the mutation as a branch-body undeclared-identifier
    /// diagnostic (branch bodies never promote implicit parameters).
    /// </summary>
    [Fact]
    public void HostMutationOfBranchBodyBetweenOperationsIsObserved()
    {
        var bodyProperties = new List<Property> { new("Target", ValueAlgorithm(101)) };
        var branchBody = new Algorithm.User(null, [], [], bodyProperties, [new Expr.Resolve("Target")]);
        var conditional = new Algorithm.Conditional(
            Parent: null,
            Opens: [],
            Branches: [new CondBranch(new Pattern.Bind("b"), branchBody)]);
        var root = new Algorithm.User(null, [], [], [new Property("Cond", conditional)], OutputBundle.Empty);

        var (_, firstDiagnostics) = ParameterDetector.Detect(root);
        Assert.DoesNotContain(firstDiagnostics, d => d.Severity == DiagnosticSeverity.Error);

        bodyProperties.RemoveAt(0);

        var (_, secondDiagnostics) = ParameterDetector.Detect(root);
        Assert.Contains(secondDiagnostics, d =>
            d.Severity == DiagnosticSeverity.Error
            && d.Code == DiagnosticCode.UndeclaredIdentifier
            && d.Message.Contains("Target"));
    }

    /// <summary>
    /// A negatively cached open target is scoped to one operation. Adding the
    /// target to the host-owned root property list between detections makes it
    /// resolvable in the next fresh chain.
    /// </summary>
    [Fact]
    public void NegativeOpenResolutionDoesNotSurviveHostMutationBetweenOperations()
    {
        var lib = Owner(new Property("X", ValueAlgorithm(101), IsPublic: true));
        var use = new Algorithm.User(
            null,
            [],
            [new Expr.Resolve("Lib")],
            [],
            [new Expr.Resolve("X")]);
        var rootProperties = new List<Property> { new("Use", use) };
        var root = new Algorithm.User(null, [], [], rootProperties, [new Expr.Resolve("Use")]);

        var (first, firstDiagnostics) = ParameterDetector.Detect(root);
        Assert.DoesNotContain(firstDiagnostics, d => d.Severity == DiagnosticSeverity.Error);
        var firstUse = Assert.IsType<Algorithm.User>(first.Properties.Single(p => p.Name == "Use").Value);
        Assert.Equal("X", Assert.Single(firstUse.Parameters).Name);

        rootProperties.Insert(0, new Property("Lib", lib));

        var (second, secondDiagnostics) = ParameterDetector.Detect(root);
        Assert.DoesNotContain(secondDiagnostics, d => d.Severity == DiagnosticSeverity.Error);
        var secondUse = Assert.IsType<Algorithm.User>(second.Properties.Single(p => p.Name == "Use").Value);
        Assert.Empty(secondUse.Parameters);
    }

    /// <summary>
    /// A scope intentionally published for concurrent reuse must prewarm every
    /// reachable mutable cache, including provider member indexes. After the
    /// prewarm, concurrent reads perform no further initialization work.
    /// </summary>
    [Fact]
    public void SharedScopePrewarmingInitializesEveryReachableLookupCache()
    {
        var exported = new Property("Exported", ValueAlgorithm(101), IsPublic: true);
        var lib = Owner(exported);
        var observations = new FrontEndTraversalObservations();
        var rootScope = ElaboratedScopeLookup.CreateScope(
            Owner(new Property("Lib", lib)),
            observations: observations);
        var sharedScope = ElaboratedScopeLookup.CreateScope(
            new Algorithm.User(
                null,
                [],
                [new Expr.Resolve("Lib")],
                [new Property("Local", ValueAlgorithm(202))],
                OutputBundle.Empty),
            rootScope);

        sharedScope.PrewarmSharedLookupCaches();
        Assert.Equal(2, observations.LookupNameIndexBuilds);
        Assert.Equal(1, observations.LookupOpenTargetResolutions);
        Assert.Equal(1, observations.LookupOpenMemberIndexBuilds);

        Parallel.For(0, 32, _ =>
        {
            Assert.NotNull(ElaboratedScopeLookup.TryLookupDirectLexicalProperty(sharedScope, "Local"));
            var hit = Assert.Single(ElaboratedScopeLookup.LookupOpenPropertyMatches(sharedScope, "Exported"));
            Assert.Same(exported, hit.Property);
        });

        Assert.Equal(2, observations.LookupNameIndexBuilds);
        Assert.Equal(1, observations.LookupOpenTargetResolutions);
        Assert.Equal(1, observations.LookupOpenMemberIndexBuilds);
    }

    /// <summary>
    /// Concurrent semantic-model builds and front-end operations share only
    /// the semantic model's static prelude level, whose caches are prewarmed
    /// (immutable after creation); every other scope chain and cache is owned
    /// by one single-threaded operation. Parallel builds and parses must
    /// therefore produce correct, independent resolutions.
    /// </summary>
    [Fact]
    public void ParallelBuildsAndDetectionsAreSafe()
    {
        const string source = """
            Lib = {
                public Exported = 101
            }
            A = {
                open Lib
                Exported
            }
            A
            """;
        var parsed = SourceProvenance.ParseValid(source).Parsed;

        Parallel.For(0, 16, _ =>
        {
            var model = SemanticModelBuilder.Build(parsed);
            var symbols = model.GetVisibleSymbolsAt(6, 5);
            Assert.Contains(symbols, s => s.Name == "Exported");

            var reparsed = Parser.Parse(source);
            Assert.False(reparsed.HasErrors);
        });
    }

    // ── completion / visible symbols stay list-enumerated ────────────────────

    /// <summary>
    /// Scope visibility flows through the SAME provider cache but keeps
    /// enumerating the ordered declaration lists: opened public members are
    /// offered with their exact provider declaration, private members are
    /// not offered, and a local same-name property shadows by identity.
    /// </summary>
    [Fact]
    public void VisibleSymbolsUseProvidersAndOrderedEnumeration()
    {
        const string source = """
            Lib = {
                public Exported = 101
                Hidden = 202
            }
            Shadow = 5
            A = {
                open Lib
                Shadow = 303
                Exported + Shadow
            }
            A
            """;
        var parsed = SourceProvenance.ParseValid(source);
        var model = SemanticModelBuilder.Build(parsed.Parsed);

        // Position inside A's body (the output row).
        var line = source.Split('\n').ToList().FindIndex(l => l.Contains("Exported + Shadow")) + 1;
        var symbols = model.GetVisibleSymbolsAt(line, 5);

        var exported = symbols.Single(s => s.Name == "Exported");
        Assert.Equal(IdentifierClassification.PropertyReference, exported.Classification);
        Assert.NotNull(exported.Declaration);
        Assert.Equal(2, exported.Declaration!.Span.StartLineNumber);

        var shadow = symbols.Single(s => s.Name == "Shadow");
        Assert.NotNull(shadow.Declaration);
        Assert.Equal(8, shadow.Declaration!.Span.StartLineNumber);

        Assert.DoesNotContain(symbols, s => s.Name == "Hidden");
    }
}
