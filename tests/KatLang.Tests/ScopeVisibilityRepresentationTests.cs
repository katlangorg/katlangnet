using System.Collections;
using System.Collections.Concurrent;
using System.Collections.ObjectModel;
using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// FE-4b: S editor scopes can LOGICALLY expose S × V visible-symbol memberships without the
/// semantic model PHYSICALLY retaining S independent V-entry snapshots. Every scope's
/// <see cref="ScopeVisibility.Symbols"/> is a distinct read-only list over an immutable,
/// canonical (hash-consed, name-ordered treap) visibility tree derived from its parent's tree by
/// the scope's own small layers, and one <see cref="VisibleSymbol"/> object serves every scope
/// that sees that symbol. The canonical hostile shape (one owner of W parameters and K local
/// properties) formerly retained (K + 2) × (W + K + 2) symbol objects; it now retains W + K.
///
/// <para>The pins separate LOGICAL memberships (the sum of list counts over scopes), the
/// PHYSICAL objects behind them (distinct views, trees, nodes, and symbol objects, read by
/// <see cref="ScopeVisibilityCensus"/>), and the construction WORK
/// (<see cref="FrontEndTraversalObservations"/>'s <c>ScopeVisibility*</c> counters, which every
/// node and layer change passes). Exactness is pinned against the retained EAGER reference
/// enumeration — the pre-FE-4b per-scope chain walk — for hand-written and generated programs,
/// under every construction path and with forced hash collisions and priority ties.</para>
/// </summary>
public class ScopeVisibilityRepresentationTests
{
    private static string Names(string prefix, int count, string separator = ", ")
        => string.Join(separator, Enumerable.Range(0, count).Select(i => $"{prefix}{i}"));

    /// <summary>FE-4a/FE-4b canonical shape: one owner of W parameters; K local properties read Base.</summary>
    private static string Canonical(int properties, int width)
        => $"O({Names("v", width)}) = {{\n    Base = {Names("v", width)}\n"
            + string.Concat(Enumerable.Range(0, properties).Select(i => $"    P{i} = Base\n"))
            + "    Base\n}\n1";

    /// <summary>K brace blocks inside the owner, each adding ONE local (base + one-symbol delta).</summary>
    private static string Blocks(int blocks, int width)
        => $"O({Names("v", width)}) = {{\n    Base = {Names("v", width)}\n"
            + string.Concat(Enumerable.Range(0, blocks).Select(i => $"    P{i} = {{\n        Q = Base\n        Q\n    }}\n"))
            + "    Base\n}\n1";

    /// <summary>W root properties and K sibling blocks; each block's body is <paramref name="body"/>(i).</summary>
    private static string Siblings(int blocks, int width, Func<int, string> body)
        => string.Concat(Enumerable.Range(0, width).Select(i => $"A{i} = {i}\n"))
            + string.Concat(Enumerable.Range(0, blocks).Select(i => $"B{i} = {{\n{body(i)}}}\n"))
            + "1";

    private static string Library(string name, int width)
        => $"{name} = {{\n" + string.Concat(Enumerable.Range(0, width).Select(i => $"    public m{i} = {i}\n")) + "    1\n}\n";

    private static string Deep(int depth, int width)
    {
        var text = new System.Text.StringBuilder();
        for (var i = 0; i < width; i++)
            text.Append($"A{i} = {i}\n");
        for (var i = 0; i < depth; i++)
        {
            text.Append($"L{i} = {{\n    X{i} = {i}\n");
            if (i % 4 == 3)
                text.Append($"    A{i % width} = {i}\n");
        }

        for (var i = depth - 1; i >= 0; i--)
            text.Append($"    X{i} + A0\n}}\n");
        return text.Append('1').ToString();
    }

    private static SemanticModel Model(string source, FrontEndTraversalObservations? observations = null)
        => SemanticModelBuilder.Build(SourceProvenance.ParseValid(source).Parsed, observations);

    private static ScopeVisibilityCensus.Report Census(SemanticModel model)
        => ScopeVisibilityCensus.Measure(model.ScopeVisibilities);

    private static int Log2(long value) => 64 - System.Numerics.BitOperations.LeadingZeroCount((ulong)Math.Max(1, value));

    // ── Structural sharing: logical memberships versus physical backing ───────────────

    /// <summary>
    /// The canonical shape: K + 2 nested scopes each LOGICALLY see W + K + 2 names, but the K + 1
    /// scopes inside the owner see exactly the same set, so they share one tree and one view; the
    /// physical nodes and symbol objects are the W + K + 2 distinct names (plus the root's one),
    /// never (K + 2) × (W + K + 2). Every scope still has its own public list.
    /// </summary>
    [Theory]
    [InlineData(64, 64)]
    [InlineData(200, 50)]
    [InlineData(50, 200)]
    public void IdenticalVisibleSets_ShareOneTreeAndOneView(int properties, int width)
    {
        var observations = new FrontEndTraversalObservations();
        var model = Model(Canonical(properties, width), observations);
        var census = Census(model);
        var names = width + properties + 2;

        Assert.Equal(properties + 3, census.Scopes);
        Assert.Equal(1 + (long)(properties + 2) * names, census.Memberships);
        Assert.Equal(census.Scopes, census.Wrappers);
        Assert.Equal(2, census.Views);
        Assert.Equal(2, census.Roots);
        Assert.InRange(census.Nodes, names, names + 1);
        Assert.Equal(names, census.Symbols);
        Assert.InRange(observations.ScopeVisibilityNodesCreated, names, 3L * names);
        Assert.InRange(observations.ScopeVisibilityLayerChanges, names, names + 2);
        Assert.InRange(observations.ScopeVisibilityStatesDerived, properties + 3, properties + 4);

        var inner = model.ScopeVisibilities.Where(scope => scope.Span is not null).ToList();
        Assert.All(inner, scope => Assert.Same(inner[0].View, scope.View));
        Assert.Equal(inner.Count, inner.Select(scope => scope.Symbols).Distinct(ReferenceEqualityComparer.Instance).Count());
    }

    /// <summary>
    /// Base + one-symbol delta: K blocks each add one local to the owner's (W + K + 2)-name set.
    /// Each block's tree shares every subtree of the owner's tree off the one changed path, so
    /// the physical nodes are the base plus K paths of tree depth — never K copies of the base.
    /// </summary>
    [Theory]
    [InlineData(64, 64)]
    [InlineData(256, 32)]
    [InlineData(32, 256)]
    public void OneLocalPerBlock_SharesTheOwnersTree(int blocks, int width)
    {
        var observations = new FrontEndTraversalObservations();
        var model = Model(Blocks(blocks, width), observations);
        var census = Census(model);
        var baseNames = width + blocks + 2;

        Assert.Equal(1 + 2 + 2L * blocks, census.Scopes);
        Assert.True(census.Memberships >= 2L * blocks * baseNames);
        Assert.Equal(baseNames + blocks, census.Symbols);
        Assert.Equal(blocks + 2, census.Roots);
        Assert.InRange(census.Nodes, baseNames, baseNames + 1 + (long)blocks * (census.MaxTreeDepth + 1));
        Assert.InRange(census.MaxTreeDepth, 1, 6 * Log2(baseNames + 1));
        Assert.InRange(observations.ScopeVisibilityNodesCreated, census.Nodes, 3L * baseNames + (long)blocks * (census.MaxTreeDepth + 1));
        Assert.InRange(observations.ScopeVisibilityLayerChanges, baseNames, baseNames + 2L * blocks + 2);
    }

    /// <summary>
    /// Base + SHADOW: each of K sibling blocks redeclares the root's <c>A0</c>. The shadow replaces
    /// one entry in O(depth) new nodes; lookup, enumeration, and declaration identity are exact
    /// per block, the root keeps its own <c>A0</c>, and no block copies the W-name base.
    /// </summary>
    [Fact]
    public void ShadowDelta_ReplacesOneEntryWithoutCopyingTheBase()
    {
        const int blocks = 96;
        const int width = 128;
        var source = Siblings(blocks, width, i => $"    A0 = {i}\n    A0 + A1\n");
        var observations = new FrontEndTraversalObservations();
        var model = Model(source, observations);
        var census = Census(model);

        Assert.InRange(census.Nodes, width + blocks, width + blocks + (long)blocks * (census.MaxTreeDepth + 1));
        var root = Assert.Single(model.ScopeVisibilities, scope => scope.Span is null);
        var rootA0 = Assert.Single(root.Symbols, symbol => symbol.Name == "A0");
        Assert.Equal(1, rootA0.Declaration!.Span.Start.Line);

        // Each block's body and its A0 body share one view (the A0 body adds nothing).
        var blockScopes = model.ScopeVisibilities
            .Where(scope => scope.View is { } view && !ReferenceEquals(view.Find("A0"), rootA0))
            .DistinctBy(scope => scope.View, ReferenceEqualityComparer.Instance)
            .ToList();
        Assert.Equal(blocks, blockScopes.Count);
        var shadows = new HashSet<DeclarationOccurrence>(ReferenceEqualityComparer.Instance);
        foreach (var scope in blockScopes)
        {
            var a0 = scope.View!.Find("A0")!;
            Assert.True(shadows.Add(a0.Declaration!));
            Assert.True(a0.Declaration!.Span.Start.Line > width);
            Assert.Equal(width + blocks, scope.Symbols.Count);
            Assert.Same(root.View!.Find("A1"), scope.View.Find("A1"));
            Assert.Equal(scope.Symbols.Select(symbol => symbol.Name).Order(StringComparer.Ordinal), scope.Symbols.Select(symbol => symbol.Name));
        }
    }

    /// <summary>
    /// Deep nesting: D levels each add one local (every fourth also shadows a root name) over a
    /// W-name root. Physical nodes stay base + D paths, and a lookup of a local, an inherited root
    /// name, a shadowed name, or a miss visits at most one tree path — bounded by the tree's own
    /// logarithmic depth at every nesting depth, never by D.
    /// </summary>
    [Theory]
    [InlineData(32)]
    [InlineData(92)]
    public void DeepNesting_KeepsLookupIndependentOfDepth(int depth)
    {
        const int width = 256;
        var observations = new FrontEndTraversalObservations();
        var model = Model(Deep(depth, width), observations);
        var census = Census(model);

        Assert.InRange(census.Nodes, width + 1, width + 1 + 3L * depth * (census.MaxTreeDepth + 1));
        Assert.InRange(census.MaxTreeDepth, 1, 6 * Log2(width + 3 * depth));
        foreach (var scope in model.ScopeVisibilities.Where(scope => scope.View is not null))
        {
            foreach (var name in new[] { "A0", "A128", "A255", "X0", "L0", "Absent", "zzz" })
                Assert.InRange(ScopeVisibilityCensus.LookupProbes(scope, name), 0, census.MaxTreeDepth);
        }

        var deepest = model.ScopeVisibilities.Where(scope => scope.View?.Find($"X{depth - 1}") is not null).MinBy(scope => scope.NestingDepth)!;
        Assert.Equal(depth, deepest.NestingDepth);
        Assert.NotNull(deepest.View!.Find($"X{depth - 1}"));
        Assert.NotNull(deepest.View.Find("A200"));
        Assert.Null(deepest.View.Find("Absent"));
    }

    /// <summary>
    /// K sibling blocks each opening the same W-member library: the level's open decisions over the
    /// same parent tree are computed once and shared, so construction work is W + O(K), not K × W.
    /// </summary>
    [Fact]
    public void SiblingOpensOfOneLibrary_ApplyTheOpenLayerOnce()
    {
        const int blocks = 128;
        const int width = 128;
        var source = Library("Lib", width) + Siblings(blocks, 0, i => $"    open Lib\n    Y = {i}\n    m0 + Y\n");
        var observations = new FrontEndTraversalObservations();
        var model = Model(source, observations);

        Assert.InRange(observations.ScopeVisibilityLayerMemoHits, blocks - 1, blocks + 4);
        Assert.InRange(observations.ScopeVisibilityLayerChanges, width, 3L * (width + blocks) + 16);
        var block = model.ScopeVisibilities.First(scope => scope.View?.Find("Y") is not null && scope.View.Find("m0") is not null);
        Assert.Equal(IdentifierClassification.PropertyReference, block.View!.Find("m127")!.Classification);
    }

    /// <summary>
    /// K sibling blocks each opening two libraries that provide the same W names: every name is
    /// ambiguous and suppressed, exactly as lookup resolves nothing; the removal layer is shared.
    /// </summary>
    [Fact]
    public void AmbiguousOpens_SuppressEveryNameAndShareTheLayer()
    {
        const int blocks = 64;
        const int width = 64;
        var source = Library("L1", width) + Library("L2", width) + Siblings(blocks, 0, i => $"    open L1, L2\n    Y = {i}\n    Y\n");
        var observations = new FrontEndTraversalObservations();
        var model = Model(source, observations);

        foreach (var scope in model.ScopeVisibilities.Where(scope => scope.View?.Find("Y") is not null))
            Assert.DoesNotContain(scope.Symbols, symbol => symbol.Name.StartsWith('m'));
        Assert.InRange(observations.ScopeVisibilityLayerMemoHits, blocks - 1, blocks + 4);
    }

    /// <summary>
    /// FE-3 integration: K owners lift one W-wide callee (one shared implicit-signature template),
    /// and each also nests a property lifting the same callee. The template table is applied once
    /// per parent tree, and not at all where the tree already holds it (the nested owner), so the
    /// visibility work stays linear while owner identity and parameter symbols are shared exactly.
    /// </summary>
    [Theory]
    [InlineData(64, 64)]
    [InlineData(128, 256)]
    public void TemplateOwners_ShareTheParameterLayer(int owners, int width)
    {
        var source = $"G = {Names("v", width)}\n"
            + string.Concat(Enumerable.Range(0, owners).Select(i => $"B{i} = {{\n    P = G\n    P, w{i}\n}}\n"))
            + "1";
        var observations = new FrontEndTraversalObservations();
        var model = Model(source, observations);
        var census = Census(model);

        Assert.InRange(observations.ScopeVisibilityLayerChanges, width, 4L * (owners + width) + 16);
        Assert.InRange(census.Symbols, width + owners, 3L * (width + owners) + 8);
        var ownerScopes = model.ScopeVisibilities.Where(scope => scope.View?.Find("P") is not null).ToList();
        Assert.True(ownerScopes.Count >= owners);
        var v0 = ownerScopes[0].View!.Find("v0")!;
        Assert.Equal(IdentifierClassification.ImplicitParameterReference, v0.Classification);
        Assert.All(ownerScopes, scope => Assert.Same(v0, scope.View!.Find("v0")));
    }

    /// <summary>
    /// A deferred module open reclassifies the open-provided names of its branch as indeterminate
    /// WITHOUT rewriting inherited entries: K blocks under the deferred open each read the eager
    /// open's W names as <see cref="IdentifierClassification.DeferredModuleReference"/> through
    /// their own reading context, sharing the tree with no per-block copy; outside the branch the
    /// same names stay property references.
    /// </summary>
    [Fact]
    public async Task DeferredBranch_ReclassifiesThroughTheReadingContext()
    {
        const int blocks = 32;
        const int width = 32;
        var modules = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["https://katlang.org/fe4b/lib.kat"] = string.Join("\n", Enumerable.Range(0, width).Select(i => $"public m{i} = {i}")),
            ["https://katlang.org/fe4b/deferred.kat"] = "public Later = 1",
        };
        var source = "open 'https://katlang.org/fe4b/lib.kat'\nF(0) = {\n    open 'https://katlang.org/fe4b/deferred.kat'\n"
            + string.Concat(Enumerable.Range(0, blocks).Select(i => $"    B{i} = {{\n        X = {i}\n        X + m0\n    }}\n"))
            + "    m0\n}\nF(n) = m0\nF(1)";
        var options = new RunOptions
        {
            DownloadCode = (url, _) => ValueTask.FromResult(modules[url]),
            AllowedHosts = ["katlang.org"],
        };
        var parsed = (await SourceProvenance.ParseValidAsync(source, options)).Parsed;
        var observations = new FrontEndTraversalObservations();
        var model = SemanticModelBuilder.Build(parsed, observations);
        var census = Census(model);

        var root = Assert.Single(model.ScopeVisibilities, scope => scope.Span is null);
        Assert.Equal(IdentifierClassification.PropertyReference, root.View!.Find("m5")!.Classification);
        var deferredBlocks = model.ScopeVisibilities
            .Where(scope => scope.View?.Find("X") is not null)
            .DistinctBy(scope => scope.View, ReferenceEqualityComparer.Instance)
            .ToList();
        Assert.Equal(blocks, deferredBlocks.Count);
        Assert.All(deferredBlocks, scope => Assert.True(scope.View!.DeferredLevels > 0));
        var twin = deferredBlocks[0].View!.Find("m5")!;
        Assert.Equal(IdentifierClassification.DeferredModuleReference, twin.Classification);
        Assert.Null(twin.Declaration);
        Assert.Null(twin.Property);
        Assert.All(deferredBlocks, scope => Assert.Same(twin, scope.View!.Find("m5")));
        Assert.InRange(census.Nodes, width, 4L * (width + blocks) + (long)blocks * (census.MaxTreeDepth + 1));
        AssertMatchesEagerReference(parsed);
    }

    /// <summary>
    /// A design-independent guard over the public build: doubling K = W roughly doubles the model's
    /// allocation for identical, one-local, shadowing, and templated shapes (the retained eager
    /// snapshots quadrupled it). Any per-scope snapshot of the visible set, or per-scope rebuild
    /// of a shared layer, quadruples it again. (Sibling opens of one library are pinned by their
    /// layer counters instead: that shape's walk-time lookup indexes are not visibility storage.)
    /// </summary>
    [Theory]
    [InlineData("canonical")]
    [InlineData("blocks")]
    [InlineData("shadow")]
    [InlineData("templates")]
    public void PublicModelBuild_AllocationGrowsLinearly(string shape)
    {
        static string Source(string shape, int n) => shape switch
        {
            "canonical" => Canonical(n, n),
            "blocks" => Blocks(n, n),
            "shadow" => Siblings(n, n, i => $"    A0 = {i}\n    A0 + A1\n"),
            "templates" => $"G = {Names("v", n)}\n" + string.Concat(Enumerable.Range(0, n).Select(i => $"B{i} = {{\n    P = G\n    P, w{i}\n}}\n")) + "1",
            _ => throw new ArgumentOutOfRangeException(nameof(shape)),
        };

        static long Allocation(string source)
        {
            var parsed = SourceProvenance.ParseValid(source).Parsed;
            _ = SemanticModelBuilder.Build(parsed);
            var before = GC.GetAllocatedBytesForCurrentThread();
            _ = SemanticModelBuilder.Build(parsed);
            return GC.GetAllocatedBytesForCurrentThread() - before;
        }

        var small = Allocation(Source(shape, 256));
        var large = Allocation(Source(shape, 512));
        var ratio = (double)large / small;
        Assert.True(ratio < 2.6, $"Doubling K = W grew the model allocation {ratio:F2}x ({small} -> {large} bytes).");
    }

    /// <summary>
    /// The retained model's visibility is O(W + K) objects, not O(K × W): at K = W = 512 the
    /// canonical shape's 527,365 logical memberships are backed by about a thousand symbol
    /// objects and nodes (the eager snapshots retained over half a million of each).
    /// </summary>
    [Fact]
    public void CanonicalShape_RetainsLinearBacking()
    {
        var model = Model(Canonical(512, 512));
        var census = Census(model);
        Assert.Equal(527_365L, census.Memberships);
        Assert.InRange(census.Nodes, 1026, 1027);
        Assert.Equal(1026, census.Symbols);
    }

    // ── Exactness: the eager reference enumeration is the oracle ─────────────────────────

    private static void AssertMatchesEagerReference(ParseResult parsed, SemanticModelBuilder.VisibilityConstructionOptions? options = null)
        => AssertMatchesEagerReference(SemanticModelBuilder.BuildWithEagerVisibilityReference(parsed, options));

    private static void AssertMatchesEagerReference(Algorithm root, SemanticModelBuilder.VisibilityConstructionOptions? options = null)
        => AssertMatchesEagerReference(SemanticModelBuilder.BuildWithEagerVisibilityReference(root, hostOperations: null, options));

    private static void AssertMatchesEagerReference((SemanticModel Model, IReadOnlyList<IReadOnlyList<VisibleSymbol>> EagerReference) built)
    {
        var (model, eager) = built;
        Assert.Equal(model.ScopeVisibilities.Count, eager.Count);
        for (var index = 0; index < eager.Count; index++)
        {
            var scope = model.ScopeVisibilities[index];
            var expected = eager[index];
            var actual = scope.Symbols;
            Assert.Equal(expected.Count, actual.Count);
            for (var i = 0; i < expected.Count; i++)
            {
                var e = expected[i];
                var a = actual[i];
                Assert.Equal(e.Name, a.Name);
                Assert.Equal(e.Classification, a.Classification);
                Assert.Same(e.Declaration, a.Declaration);
                Assert.Same(e.Property, a.Property);
                Assert.Equal(e.Members.Count, a.Members.Count);
                for (var m = 0; m < e.Members.Count; m++)
                    Assert.Same(e.Members[m], a.Members[m]);
                Assert.Same(a, scope.View?.Find(e.Name) ?? a);
            }

            // Enumeration, indexing, and copying agree element by element, in ordinal name order.
            Assert.Equal(actual.Select(symbol => symbol.Name).Order(StringComparer.Ordinal), actual.Select(symbol => symbol.Name));
            var enumerated = new List<VisibleSymbol>(actual.Count);
            foreach (var symbol in actual)
                enumerated.Add(symbol);
            var copied = new VisibleSymbol[actual.Count];
            ((ICollection<VisibleSymbol>)actual).CopyTo(copied, 0);
            for (var i = 0; i < actual.Count; i++)
            {
                Assert.Same(actual[i], enumerated[i]);
                Assert.Same(actual[i], copied[i]);
            }

            if (scope.View is { } view)
            {
                foreach (var absent in new[] { "", "Absent", "zz_absent", "sum", "Math", "if", "é" })
                {
                    if (expected.All(symbol => symbol.Name != absent))
                        Assert.Null(view.Find(absent));
                }
            }
        }

        // Completion: the scope's symbols, then the prelude symbols they do not shadow, in order.
        foreach (var scope in model.ScopeVisibilities)
        {
            var position = scope.Span?.Start ?? new SourcePosition(1, 1);
            var merged = model.GetVisibleSymbolsAt(position);
            var at = model.FindScopeAt(position);
            var names = at.Symbols.Select(symbol => symbol.Name).ToHashSet(StringComparer.Ordinal);
            var expectedMerged = at.Symbols.Concat(model.PreludeSymbols.Where(symbol => !names.Contains(symbol.Name))).ToList();
            Assert.Equal(expectedMerged.Count, merged.Count);
            for (var i = 0; i < merged.Count; i++)
                Assert.Same(expectedMerged[i], merged[i]);
        }
    }

    public static TheoryData<string> HandWrittenPrograms() =>
    [
        "x = 1\nA = {\n    x = 2\n    x + 1\n}\nB = x\nA + B",
        "x = 1\ny = 2\nA = {\n    x = 10\n    B = {\n        y = 20\n        C = {\n            x = 100\n            x + y\n        }\n        C + x\n    }\n    B\n}\nA + x + y",
        "sum = 5\ncount = 3\nF(a) = {\n    if = a\n    if + sum + count\n}\nF(2)",
        "zeta = 1\nAlpha = 2\n_under = 3\nalpha = 4\nZ9 = 5\nz10 = 6\nB = {\n    beta = 7\n    Beta = 8\n    _a = 9\n    zeta + Alpha + _under + alpha + Z9 + z10 + beta + Beta + _a\n}\nB",
        "é = 1\nÄb = 2\nω = 3\nB = {\n    ÿ = 4\n    é + Äb + ω + ÿ\n}\nB",
        "F(a, b, *rest) = {\n    G = a + b\n    G + rest.count\n}\nF(1, 2, 3, 4)",
        "P((x, y)) = {\n    Q = x * y\n    Q\n}\nP((3, 4))",
        "G = a + b\nH = {\n    K = G\n    K + c\n}\nH(1, 2, 3)",
        "F(0) = 0\nF((a, b)) = {\n    S = a + b\n    S\n}\nF(n) = {\n    T = n * 2\n    T\n}\nF((1, 2)) + F(5)",
        "Lib = {\n    public Rate = 2\n    Hidden = 3\n    1\n}\nUse = {\n    open Lib\n    Rate * 10\n}\nUse",
        "L1 = {\n    public X = 1\n    public Only1 = 2\n    1\n}\nL2 = {\n    public X = 3\n    public Only2 = 4\n    1\n}\nU = {\n    open L1, L2\n    Only1 + Only2\n}\nU",
        "L1 = {\n    public X = 1\n    1\n}\nU = {\n    open L1, L1\n    X\n}\nU",
        "Lib = {\n    public X = 1\n    public Y = 2\n    1\n}\nU = {\n    open Lib\n    X = 10\n    X + Y\n}\nV = {\n    open Lib\n    W = {\n        open Lib\n        X + Y\n    }\n    W\n}\nU + V",
        "Lib = {\n    public sum = 1\n    public Other = 2\n    1\n}\nU = {\n    open Lib\n    sum((Other, 1))\n}\nU",
        "Outer = {\n    public A = 1\n    public Inner = {\n        public B = 2\n        1\n    }\n    1\n}\nU = {\n    open Outer, Outer.Inner\n    A + B\n}\nU",
        "L1 = {\n    public X = 1\n    1\n}\nL2 = {\n    public X = 2\n    1\n}\nU = {\n    open L1\n    V = {\n        open L2\n        X\n    }\n    V + X\n}\nU",
        "L1 = {\n    public X = 1\n    1\n}\nL2 = {\n    public X = 2\n    1\n}\nU = {\n    open L1, L2\n    V = {\n        open L1\n        X\n    }\n    V\n}\nU",
        "U = {\n    open Math\n    Sqrt(Pi) + sin(1)\n}\nU",
        "U = {\n    open Lib\n    Rate + 1\n}\nLib = {\n    public Rate = 2\n    public Deep = {\n        public E = 1\n        1\n    }\n    1\n}\nU",
        "A0 = 1\nF(0) = {\n    X = 1\n    X + A0\n}\nF(1) = {\n    X = 2\n    X + A0\n}\nF(n) = n\nF(0) + F(1)",
        "F(x) = if(x > 0, {\n    Y = x\n    Y + 1\n}, {\n    Y = 0 - x\n    Y\n})\nF(3) + F(-2)",
        "G = v0 + v1 + v2\nB0 = G + 1\nB1 = {\n    P = G\n    P + w\n}\nB2 = G * 2\nB0(1, 2, 3) + B1(1, 2, 3, 4) + B2(1, 2, 3)",
        "G = v0 + v1\nO(v0, v1) = {\n    P0 = G\n    P1 = {\n        Q = G\n        Q\n    }\n    P0 + P1\n}\nO(1, 2)",
        "x, *y = (1, 2, 3)\nB = {\n    a, b = (4, 5)\n    a + b + x\n}\nB + y.count",
        "B = {\n    pi = 3\n    pi + Pi\n}\nC = {\n    open Math\n    Pi + pi\n}\nB + C",
        Canonical(9, 7),
        Blocks(9, 7),
        Deep(12, 9),
        Library("Lib", 9) + Siblings(5, 4, i => $"    open Lib\n    m{i} = {i}\n    m0 + A0\n"),
        Library("L1", 6) + Library("L2", 6) + Siblings(4, 3, i => $"    open L1, L2\n    Y = {i}\n    Y\n"),
    ];

    [Theory]
    [MemberData(nameof(HandWrittenPrograms))]
    public void HandWrittenPrograms_MatchTheEagerReference(string source)
    {
        var parsed = SourceProvenance.ParseValid(source).Parsed;
        AssertMatchesEagerReference(parsed);
        AssertMatchesEagerReference(parsed, new(ForceBulk: true));
        AssertMatchesEagerReference(parsed, new(ForceBulk: false));
        AssertMatchesEagerReference(parsed, new(CollideNodeHashes: true));
        AssertMatchesEagerReference(parsed, new(PriorityOverride: static _ => 0));
    }

    public static TheoryData<string> ModuleAndDeferredPrograms() =>
    [
        "open 'https://katlang.org/v/lib.kat'\nA = {\n    Total + Rate\n}\nB = {\n    Total = 100\n    Total + Rate\n}\nA + B",
        "A = {\n    open 'https://katlang.org/v/lib.kat'\n    Total\n}\nB = {\n    open 'https://katlang.org/v/lib.kat'\n    Rate\n}\nA + B",
        "open 'https://katlang.org/v/lib.kat', 'https://katlang.org/v/lib2.kat'\nOther + Rate",
        "M = load('https://katlang.org/v/lib.kat')\nU = {\n    open M\n    Total + M.Rate\n}\nU",
        "open 'https://katlang.org/v/lib.kat'\nF(0) = {\n    open 'https://katlang.org/v/deferred.kat'\n    Later + Total\n}\nF(1) = Total\nF(1)",
        "open 'https://katlang.org/v/lib.kat'\nF(0) = {\n    open 'https://katlang.org/v/deferred.kat'\n    A = {\n        X = 1\n        X + Total\n    }\n    B = {\n        Rate = 5\n        Rate + Total\n    }\n    A + B\n}\nF(n) = Total\nF(1)",
        "F(0) = {\n    open M\n    M = load('https://katlang.org/v/deferred.kat')\n    Later + 1\n}\nF(n) = n\nF(1)",
        "Lib = {\n    public Rate = 2\n    1\n}\nF(0) = {\n    open Lib\n    G = {\n        open 'https://katlang.org/v/deferred.kat'\n        Rate + Later\n    }\n    H = Rate\n    G + H\n}\nF(n) = n\nF(1)",
        // An eager open INSIDE a deferred branch decides its names below the deferred level.
        "open 'https://katlang.org/v/lib.kat'\nL2 = {\n    public Total = 3\n    public Other = 4\n    1\n}\nF(0) = {\n    open 'https://katlang.org/v/deferred.kat'\n    G = {\n        open L2\n        H = {\n            Total + Rate + Other\n        }\n        H\n    }\n    G\n}\nF(n) = n\nF(1)",
        // A deferred owner nested inside another deferred branch, with re-opens at every level.
        "open 'https://katlang.org/v/lib.kat'\nF(0) = {\n    open 'https://katlang.org/v/deferred.kat'\n    G(0) = {\n        open 'https://katlang.org/v/lib2.kat'\n        K = {\n            open 'https://katlang.org/v/deferred2.kat'\n            Total + Other\n        }\n        K\n    }\n    G(n) = Rate\n    G(0)\n}\nF(n) = n\nF(1)",
        "open 'https://katlang.org/v/lib.kat'\nx, y = (1, 2)\nF(0) = {\n    open 'https://katlang.org/v/deferred.kat'\n    a, b = (3, 4)\n    B = {\n        X = 1\n        X + Total + a\n    }\n    B\n}\nF(n) = Total + x\nF(1)",
        // Two inline blocks opening one library over the SAME parent tree — one outside, one inside a
        // deferred owner that adds no names: the open layer's deferred context must keep them apart.
        "Lib = {\n    public R = 1\n    1\n}\nP = {\n    {\n        open Lib\n        R\n    } + 1\n}\nF(0) = {\n    open 'https://katlang.org/v/deferred.kat'\n    {\n        open Lib\n        R\n    } + 1\n}\nF(n) = n\nP + F(1)",
    ];

    [Theory]
    [MemberData(nameof(ModuleAndDeferredPrograms))]
    public async Task ModuleAndDeferredPrograms_MatchTheEagerReference(string source)
    {
        var modules = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["https://katlang.org/v/lib.kat"] = "public Total = 5\nFee = 9\npublic Rate = 2\npublic Sub = {\n    public Deep = 3\n    Hidden = 4\n    1\n}",
            ["https://katlang.org/v/lib2.kat"] = "public Total = 7\npublic Other = 8",
            ["https://katlang.org/v/deferred.kat"] = "public Later = 1",
            ["https://katlang.org/v/deferred2.kat"] = "public Later = 2",
        };
        var options = new RunOptions { DownloadCode = (url, _) => ValueTask.FromResult(modules[url]), AllowedHosts = ["katlang.org"] };
        var parsed = (await SourceProvenance.ParseValidAsync(source, options)).Parsed;
        AssertMatchesEagerReference(parsed);
        AssertMatchesEagerReference(parsed, new(ForceBulk: true));
        AssertMatchesEagerReference(parsed, new(PriorityOverride: static _ => 1));
    }

    /// <summary>
    /// HOST-BUILT (a parser-produced synthetic name is never public, so no source reaches this): an
    /// opened library exposes a PUBLIC member spelled like the document's synthetic deconstruction
    /// source. Under a deferred module open, eager lookup meets that synthetic DIRECT property first
    /// and keeps the opened name determinate while the library's other opened names become
    /// indeterminate — the persistent view's synthetic-name shield must reproduce exactly that.
    /// </summary>
    [Fact]
    public async Task SyntheticNameShield_KeepsTheOpenedNameDeterminate()
    {
        const string source = "open Lib\na, b = (1, 2)\nLib = {\n    public q = 1\n    1\n}\nF(0) = {\n    open 'https://katlang.org/v/deferred.kat'\n    B = {\n        X = 1\n        X + q\n    }\n    B\n}\nF(n) = n\nF(1)";
        var options = new RunOptions { DownloadCode = static (_, _) => ValueTask.FromResult("public Later = 1"), AllowedHosts = ["katlang.org"] };
        var root = (await SourceProvenance.ParseValidAsync(source, options)).Root;
        var synthetic = Assert.Single(root.Properties, property => property.Name.StartsWith('$'));
        var lib = Assert.Single(root.Properties, property => property.Name == "Lib");
        var libBody = Assert.IsType<Algorithm.User>(lib.Value);
        var q = Assert.Single(libBody.Properties, property => property.Name == "q");
        var hostLib = lib with { Value = libBody with { Properties = [q, new Property(synthetic.Name, q.Value, IsPublic: true)] } };
        var hostRoot = root with { Properties = [.. root.Properties.Select(property => ReferenceEquals(property, lib) ? hostLib : property)] };

        AssertMatchesEagerReference(hostRoot);
        var model = SemanticModelBuilder.Build(hostRoot);
        var block = model.ScopeVisibilities.Where(scope => scope.View?.Find("X") is not null).MinBy(scope => scope.NestingDepth)!;
        Assert.True(block.View!.DeferredLevels > 0);
        Assert.Equal(IdentifierClassification.DeferredModuleReference, block.View.Find("q")!.Classification);
        Assert.Equal(IdentifierClassification.PropertyReference, block.View.Find(synthetic.Name)!.Classification);
    }

    /// <summary>
    /// HOST-BUILT (the front end never lifts a template name through a nearer binding of it): an
    /// owner applies a shared FE-3 template table, a nested frame rebinds one of its names with an
    /// explicit parameter of its own, and a deeper owner over the SAME template must see the
    /// template's binding again — the applied-table tracking has to drop the table as soon as a
    /// direct layer overrides one of its names, instead of skipping the re-application.
    /// </summary>
    [Fact]
    public void OverriddenTemplateName_IsReappliedBelowTheOverride()
    {
        const string source = "G = u + t\nO = {\n    N = {\n        D = G\n        D\n    }\n    N + G\n}\n1";
        var root = SourceProvenance.ParseValid(source).Root;
        var o = Assert.Single(root.Properties, property => property.Name == "O");
        var oBody = Assert.IsType<Algorithm.User>(o.Value);
        var n = Assert.Single(oBody.Properties, property => property.Name == "N");
        var nBody = Assert.IsType<Algorithm.User>(n.Value);
        var dBody = Assert.IsType<Algorithm.User>(Assert.Single(nBody.Properties, property => property.Name == "D").Value);
        Assert.Same(oBody.ParameterPatterns, dBody.ParameterPatterns);
        var rebound = nBody with
        {
            ParameterPatterns = [new CaptureParameterPattern(new ParameterDeclaration("u", n.DeclarationSpans[0]))],
            HasExplicitParameterList = true,
        };
        var hostO = o with { Value = oBody with { Properties = [.. oBody.Properties.Select(property => ReferenceEquals(property, n) ? n with { Value = rebound } : property)] } };
        var hostRoot = root with { Properties = [.. root.Properties.Select(property => ReferenceEquals(property, o) ? hostO : property)] };

        AssertMatchesEagerReference(hostRoot);
        var model = SemanticModelBuilder.Build(hostRoot);
        var nScope = Assert.Single(model.ScopeVisibilities, scope => scope.NestingDepth == 2 && scope.View?.Find("D") is not null);
        var dScope = model.ScopeVisibilities.Where(scope => scope.NestingDepth == 3 && scope.View?.Find("D") is not null).First();
        Assert.Equal(IdentifierClassification.ExplicitParameterReference, nScope.View!.Find("u")!.Classification);
        Assert.Equal(IdentifierClassification.ImplicitParameterReference, dScope.View!.Find("u")!.Classification);
        Assert.Same(model.ScopeVisibilities.Single(scope => scope.NestingDepth == 1 && scope.View?.Find("N") is not null && scope.View.Find("D") is null).View!.Find("u"), dScope.View.Find("u"));
    }

    [Fact]
    public void HostOperations_AreOfferedLikePreludeNames()
    {
        var operations = HostOperations.Create([HostOperation.Create("Tick", static (args, _) => args[0], "v")]);
        var parsed = Parser.Parse("Tick(1) + {\n    Tick = 5\n    Tick\n}", new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors);
        AssertMatchesEagerReference(parsed);
    }

    /// <summary>
    /// Generated programs (nested and sibling blocks, same-name shadows across levels, explicit and
    /// implicit parameters, clause families with binders, opens of one or two libraries including
    /// ambiguity and re-opening, deconstruction synthetics) — each compared scope by scope against
    /// the eager reference, on the default, bulk, incremental, colliding-hash, and tied-priority
    /// construction paths.
    /// </summary>
    [Fact]
    public void GeneratedPrograms_MatchTheEagerReference()
    {
        for (var seed = 1; seed <= 160; seed++)
        {
            var source = ProgramGenerator.Generate(seed);
            var parsed = Parser.Parse(source);
            Assert.False(parsed.HasErrors, $"seed {seed} produced an invalid program:\n{source}\n{string.Join("\n", parsed.Diagnostics.Select(d => d.Message))}");
            AssertMatchesEagerReference(parsed);
            AssertMatchesEagerReference(parsed, new(ForceBulk: seed % 2 == 0));
            if (seed % 5 == 0)
            {
                AssertMatchesEagerReference(parsed, new(CollideNodeHashes: true));
                AssertMatchesEagerReference(parsed, new(PriorityOverride: static name => (name?.Length ?? 0) % 3));
            }
        }
    }

    /// <summary>A small random program generator whose output is always a legal document.</summary>
    private sealed class ProgramGenerator
    {
        private static readonly string[] Pool = ["x", "y", "A", "Z", "_q", "b1", "B1", "sum", "pi", "é"];
        private readonly Random _random;
        private readonly System.Text.StringBuilder _text = new();
        private int _fresh;

        private ProgramGenerator(int seed) => _random = new Random(seed);

        public static string Generate(int seed) => new ProgramGenerator(seed).Program();

        private string Program()
        {
            _text.Append("L1 = {\n    public x = 1\n    public y = 2\n    public m = 3\n    hidden = 4\n    1\n}\n");
            _text.Append("L2 = {\n    public x = 5\n    public w = 6\n    public m = 7\n    1\n}\n");
            _text.Append("G = u + t\n");
            Body(depth: 0, parameters: [], indent: "");
            _text.Append("1");
            return _text.ToString();
        }

        private void Body(int depth, HashSet<string> parameters, string indent)
        {
            var declared = new HashSet<string>(StringComparer.Ordinal);
            if (depth > 0)
            {
                var opens = _random.Next(6);
                if (opens == 1) _text.Append(indent).Append("open L1\n");
                else if (opens == 2) _text.Append(indent).Append("open L1, L2\n");
                else if (opens == 3) _text.Append(indent).Append("open L2, L1, L1\n");
                else if (opens == 4) _text.Append(indent).Append("open L2\n");
            }

            var count = depth == 0 ? 3 + _random.Next(4) : _random.Next(4);
            for (var i = 0; i < count; i++)
            {
                var name = PickName(parameters, declared);
                if (name is null)
                    continue;
                declared.Add(name);
                var kind = depth >= 3 ? 0 : _random.Next(7);
                switch (kind)
                {
                    case 0:
                        _text.Append(indent).Append(name).Append(" = ").Append(_random.Next(9)).Append('\n');
                        break;
                    case 1:
                    case 2:
                        _text.Append(indent).Append(name).Append(" = {\n");
                        Body(depth + 1, parameters, indent + "    ");
                        _text.Append(indent).Append("    1\n").Append(indent).Append("}\n");
                        break;
                    case 3:
                    {
                        var p = "p" + _fresh++;
                        var inner = new HashSet<string>(parameters, StringComparer.Ordinal) { p };
                        _text.Append(indent).Append(name).Append('(').Append(p).Append(") = {\n");
                        Body(depth + 1, inner, indent + "    ");
                        _text.Append(indent).Append("    ").Append(p).Append('\n').Append(indent).Append("}\n");
                        break;
                    }
                    case 4:
                        _text.Append(indent).Append(name).Append(" = {\n").Append(indent).Append("    Q = G\n").Append(indent).Append("    Q\n").Append(indent).Append("}\n");
                        break;
                    case 5:
                    {
                        var a = "k" + _fresh++;
                        var c = "k" + _fresh++;
                        declared.Add(a);
                        declared.Add(c);
                        _text.Append(indent).Append(a).Append(", ").Append(c).Append(" = (1, 2)\n");
                        break;
                    }

                    default:
                    {
                        // A clause family: a literal clause and a binder clause whose body nests a scope.
                        var binder = "k" + _fresh++;
                        var inner = new HashSet<string>(parameters, StringComparer.Ordinal) { binder };
                        _text.Append(indent).Append(name).Append("(0) = 0\n");
                        _text.Append(indent).Append(name).Append('(').Append(binder).Append(") = {\n");
                        Body(depth + 1, inner, indent + "    ");
                        _text.Append(indent).Append("    ").Append(binder).Append('\n').Append(indent).Append("}\n");
                        break;
                    }
                }
            }
        }

        private string? PickName(HashSet<string> parameters, HashSet<string> declared)
        {
            for (var attempt = 0; attempt < 6; attempt++)
            {
                var name = _random.Next(3) == 0 ? "n" + _fresh++ : Pool[_random.Next(Pool.Length)];
                if (!parameters.Contains(name) && !declared.Contains(name) && name is not "L1" and not "L2" and not "G")
                    return name;
            }

            return null;
        }
    }

    // ── Canonical trees: path and derivation independence ───────────────────────────────

    private static VisibleSymbol Symbol(string name) => new(name, IdentifierClassification.PropertyReference, null, null);

    /// <summary>
    /// The same content yields the SAME root object however it is derived: in any insertion order,
    /// by bulk rebuild or incremental change, and across the bulk threshold boundary (the size that
    /// selects the path changes only speed). Removal restores the earlier root.
    /// </summary>
    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    [InlineData(2)]
    public void CanonicalTrees_AreIndependentOfPathAndOrder(int priorityMode)
    {
        Func<string?, int>? priority = priorityMode switch
        {
            1 => static _ => 7,
            2 => static name => (name?.Length ?? 0) % 2,
            _ => null,
        };
        var trees = new VisibilityTreeBuilder(observations: null) { PriorityOverride = priority };
        var symbols = Enumerable.Range(0, 200).Select(i => Symbol($"s{i:D3}")).ToArray();
        var entries = symbols.Select(symbol => trees.Entry(symbol, VisibilityEntry.DirectMeta, null)).ToArray();

        VisibilityNode? forward = null;
        foreach (var entry in entries)
            forward = trees.Set(forward, entry);
        VisibilityNode? backward = null;
        foreach (var entry in Enumerable.Reverse(entries))
            backward = trees.Set(backward, entry);
        var shuffled = entries.OrderBy(entry => entry.Name.GetHashCode()).ToArray();
        VisibilityNode? random = null;
        foreach (var entry in shuffled)
            random = trees.Set(random, entry);
        var bulk = trees.Build(entries.ToList());

        Assert.Same(forward, backward);
        Assert.Same(forward, random);
        Assert.Same(forward, bulk);
        Assert.Equal(symbols, VisibilityTree.InOrder(forward).Select(node => node.Symbol));

        // Layers straddling the bulk threshold (both of its conditions) take the path the size
        // selects, and every path yields the canonical tree of the union: the same root object in
        // one builder, the same content in another.
        var threshold = VisibilityTreeBuilder.BulkMinimumChanges;
        foreach (var (size, baseSize) in new[] { (threshold - 1, 0), (threshold, 0), (threshold + 1, 0), (threshold, threshold * VisibilityTreeBuilder.BulkDivisor), (threshold, threshold * VisibilityTreeBuilder.BulkDivisor + 1), (24, 199), (25, 199), (26, 199) })
        {
            var observations = new FrontEndTraversalObservations();
            var observed = new VisibilityTreeBuilder(observations) { PriorityOverride = priority };
            var baseEntries = entries.Take(baseSize).Select(entry => observed.Entry(entry.Symbol, entry.Meta, null)).ToList();
            var baseRoot = observed.Build(baseEntries);
            var extra = Enumerable.Range(0, size).Select(i => observed.Entry(Symbol($"t{i:D3}"), VisibilityEntry.DirectMeta, null)).ToList();
            var bulkBuildsBefore = observations.ScopeVisibilityBulkBuilds;
            var defaultPath = observed.Apply(baseRoot, extra.Select(VisibilityDelta.Set).ToList());
            var expectBulk = size >= threshold && (long)size * VisibilityTreeBuilder.BulkDivisor >= baseSize;
            Assert.Equal(expectBulk, VisibilityTreeBuilder.UsesBulkPath(size, baseSize));
            Assert.Equal(expectBulk ? 1 : 0, observations.ScopeVisibilityBulkBuilds - bulkBuildsBefore);
            Assert.Same(defaultPath, observed.Build(baseEntries.Concat(extra).OrderBy(entry => entry.Name, StringComparer.Ordinal).ToList()));
            Assert.Same(defaultPath, observed.Apply(baseRoot, extra.Select(VisibilityDelta.Set).ToList()));

            var viaBulk = new VisibilityTreeBuilder(null) { ForceBulk = true, PriorityOverride = priority };
            var viaIncremental = new VisibilityTreeBuilder(null) { ForceBulk = false, PriorityOverride = priority };
            AssertSameContent(defaultPath, viaBulk.Apply(Rebuild(viaBulk, baseRoot), extra.Select(VisibilityDelta.Set).ToList()));
            AssertSameContent(defaultPath, viaIncremental.Apply(Rebuild(viaIncremental, baseRoot), extra.Select(VisibilityDelta.Set).ToList()));
        }

        var withExtra = trees.Set(forward, trees.Entry(Symbol("zz"), VisibilityEntry.DirectMeta, null));
        Assert.Same(forward, trees.Remove(withExtra, "zz"));
        Assert.Same(forward, trees.Remove(forward, "absent"));
        Assert.Same(forward, trees.Set(forward, entries[17]));
    }

    private static VisibilityNode? Rebuild(VisibilityTreeBuilder trees, VisibilityNode? root)
        => trees.Build(VisibilityTree.InOrder(root).Select(node => new VisibilityEntry(node)).ToList());

    private static void AssertSameContent(VisibilityNode? expected, VisibilityNode? actual)
    {
        var e = VisibilityTree.InOrder(expected).ToList();
        var a = VisibilityTree.InOrder(actual).ToList();
        Assert.Equal(e.Count, a.Count);
        for (var i = 0; i < e.Count; i++)
        {
            Assert.Same(e[i].Symbol, a[i].Symbol);
            Assert.Equal(e[i].Meta, a[i].Meta);
        }
    }

    /// <summary>
    /// Node interning compares every component: with every intern key hashing alike, distinct
    /// entries, metas, and children never merge, and equal content still shares one node.
    /// </summary>
    [Fact]
    public void CollidingInternHashes_NeverMergeDistinctNodes()
    {
        var trees = new VisibilityTreeBuilder(observations: null, collideNodeHashes: true);
        var sameName = Symbol("x");
        var otherDeclaration = new VisibleSymbol("x", IdentifierClassification.PropertyReference, new DeclarationOccurrence("x", new SourceSpan(1, 1, 1, 2), OccurrenceKind.PropertyDefinition), null);
        var direct = trees.Make(trees.Entry(sameName, VisibilityEntry.DirectMeta, null), null, null);
        var open = trees.Make(trees.Entry(sameName, VisibilityEntry.OpenMeta(0), null), null, null);
        var otherSymbol = trees.Make(trees.Entry(otherDeclaration, VisibilityEntry.DirectMeta, null), null, null);
        Assert.NotSame(direct, open);
        Assert.NotSame(direct, otherSymbol);
        Assert.NotSame(open, otherSymbol);
        Assert.Same(direct, trees.Make(trees.Entry(sameName, VisibilityEntry.DirectMeta, null), null, null));
        Assert.Same(open, trees.Make(trees.Entry(sameName, VisibilityEntry.OpenMeta(0), null), null, null));
        Assert.NotSame(trees.Make(trees.Entry(sameName, VisibilityEntry.DirectMeta, null), direct, null), trees.Make(trees.Entry(sameName, VisibilityEntry.DirectMeta, null), null, direct));

        var many = Enumerable.Range(0, 64).Select(i => trees.Entry(Symbol($"n{i:D2}"), VisibilityEntry.DirectMeta, null)).ToList();
        var root = trees.Build(many);
        Assert.Equal(many.Select(entry => entry.Symbol), VisibilityTree.InOrder(root).Select(node => node.Symbol));
    }

    // ── Identity: same spelling is never the same symbol ─────────────────────────────────

    /// <summary>
    /// Sibling blocks declaring the same local spelling, same-named parameters of different owners,
    /// and a local shadowing an opened member: each scope offers ITS declaration; symbols are
    /// shared only when they are the same declaration (the same object across every scope).
    /// </summary>
    [Fact]
    public void SameSpelling_NeverSharesADeclaration()
    {
        const string source = "Lib = {\n    public X = 1\n    1\n}\nA = {\n    X = 2\n    X\n}\nB = {\n    X = 3\n    X\n}\nC = {\n    open Lib\n    X\n}\nF(p) = {\n    G = p\n    G\n}\nH(p) = {\n    K = p\n    K\n}\nA + B + C + F(1) + H(2)";
        var model = Model(source);
        var xs = model.ScopeVisibilities
            .Select(scope => scope.View?.Find("X"))
            .Where(symbol => symbol is not null)
            .Distinct(ReferenceEqualityComparer.Instance)
            .Cast<VisibleSymbol>()
            .ToList();
        Assert.Equal(3, xs.Count);
        Assert.Equal(3, xs.Select(symbol => symbol.Declaration).Distinct(ReferenceEqualityComparer.Instance).Count());
        var ps = model.ScopeVisibilities.Select(scope => scope.View?.Find("p")).Where(symbol => symbol is not null).Distinct(ReferenceEqualityComparer.Instance).ToList();
        Assert.Equal(2, ps.Count);

        var root = Assert.Single(model.ScopeVisibilities, scope => scope.Span is null);
        var lib = root.View!.Find("Lib")!;
        Assert.All(model.ScopeVisibilities.Where(scope => scope.View?.Find("Lib") is not null), scope => Assert.Same(lib, scope.View!.Find("Lib")));
    }

    // ── Public contract ─────────────────────────────────────────────────────────────────

    /// <summary>
    /// The public surface is unchanged: a non-empty scope's <see cref="ScopeVisibility.Symbols"/> is
    /// still a <see cref="ReadOnlyCollection{T}"/> (a distinct one per scope), an empty one is still
    /// the shared empty array, <c>ToString</c> prints the same text, and record equality stays per
    /// scope — two scopes over one shared view are never equal, a <c>with</c> copy is, and an empty
    /// builder scope equals a host-constructed empty scope exactly as before.
    /// </summary>
    [Fact]
    public void PublicShapeEqualityAndText_AreUnchanged()
    {
        var model = Model(Canonical(8, 8) + "\nE = {\n    1\n}");
        var inner = model.ScopeVisibilities.Where(scope => scope.Span is not null && scope.Symbols.Count > 0).ToList();
        var sharing = inner.GroupBy(scope => scope.View, ReferenceEqualityComparer.Instance).First(group => group.Count() > 1).ToList();

        foreach (var scope in inner)
        {
            Assert.Equal(typeof(ReadOnlyCollection<VisibleSymbol>), scope.Symbols.GetType());
            Assert.Contains("Symbols = System.Collections.ObjectModel.ReadOnlyCollection`1[KatLang.Semantics.VisibleSymbol]", scope.ToString());
            Assert.Equal(scope, scope with { });
            Assert.Equal(scope.GetHashCode(), (scope with { }).GetHashCode());
            Assert.Same(scope.Symbols, (scope with { }).Symbols);
        }

        Assert.NotSame(sharing[0].Symbols, sharing[1].Symbols);
        Assert.NotEqual(sharing[0], sharing[1]);
        Assert.NotEqual(sharing[0].GetHashCode(), sharing[1].GetHashCode());
        var hostCopy = new ScopeVisibility(sharing[0].Span, sharing[0].Symbols, sharing[0].NestingDepth);
        Assert.NotEqual(sharing[0], hostCopy);
        Assert.Equal(sharing[0].Symbols, hostCopy.Symbols);

        var empty = new ScopeVisibility(null, [], 0);
        var builderEmpty = SemanticModelBuilder.Build(SourceProvenance.ParseValid("1").Parsed).ScopeVisibilities.Single();
        Assert.Same(Array.Empty<VisibleSymbol>(), builderEmpty.Symbols);
        Assert.Equal(empty, builderEmpty);
        Assert.Equal(empty.GetHashCode(), builderEmpty.GetHashCode());
        Assert.Equal(empty.ToString(), builderEmpty.ToString());
    }

    /// <summary>
    /// REVIEWED FE-4b change: a symbol visible in several scopes is ONE <see cref="VisibleSymbol"/>
    /// object, so it is reference- and record-equal across scopes — also when it carries members
    /// (formerly each scope copied the members list, which alone made such copies unequal).
    /// Distinct declarations of one spelling stay unequal.
    /// </summary>
    [Fact]
    public void SharedSymbols_AreOneObjectAcrossScopes()
    {
        const string source = "Lib = {\n    public Rate = 2\n    Sub = {\n        public Deep = 1\n        1\n    }\n    1\n}\nA = {\n    Y = {\n        Q = 1\n        Q\n    }\n    Y\n}\nB = {\n    Y = {\n        Q = 1\n        Q\n    }\n    Y\n}\nA + B";
        var model = Model(source);
        var libs = model.ScopeVisibilities.Select(scope => scope.View?.Find("Lib")).Where(symbol => symbol is not null).ToList();
        Assert.True(libs.Count >= 3);
        Assert.All(libs, lib => Assert.Same(libs[0], lib));
        Assert.NotEmpty(libs[0]!.Members);
        Assert.Equal(libs[0], libs[^1]);

        // Two member-bearing locals of one spelling (A.Y and B.Y, each with member Q) stay unequal.
        var ys = model.ScopeVisibilities
            .Select(scope => scope.View?.Find("Y"))
            .Where(symbol => symbol is not null)
            .Distinct(ReferenceEqualityComparer.Instance)
            .Cast<VisibleSymbol>()
            .ToList();
        Assert.Equal(2, ys.Count);
        Assert.All(ys, y => Assert.Equal("Q", Assert.Single(y.Members).Name));
        Assert.NotEqual(ys[0], ys[1]);
    }

    /// <summary>
    /// Shared backing has no mutation route: every generic and non-generic list and collection
    /// operation that would write throws, the backing view is not reachable through the public
    /// wrapper, and contents are unchanged afterwards — for scope lists and completion lists.
    /// </summary>
    [Fact]
    public void SharedLists_HaveNoMutationRoute()
    {
        var model = Model(Canonical(6, 6));
        var scope = model.ScopeVisibilities.First(candidate => candidate.Span is not null);
        foreach (var list in new[] { scope.Symbols, model.GetVisibleSymbolsAt(scope.Span!.Value.Start) })
        {
            var before = list.ToArray();
            var generic = Assert.IsAssignableFrom<IList<VisibleSymbol>>(list);
            Assert.True(generic.IsReadOnly);
            Assert.Throws<NotSupportedException>(() => generic[0] = before[1]);
            Assert.Throws<NotSupportedException>(() => generic.Add(before[0]));
            Assert.Throws<NotSupportedException>(() => generic.Insert(0, before[0]));
            Assert.Throws<NotSupportedException>(() => generic.Remove(before[0]));
            Assert.Throws<NotSupportedException>(() => generic.RemoveAt(0));
            Assert.Throws<NotSupportedException>(generic.Clear);
            var nonGeneric = Assert.IsAssignableFrom<IList>(list);
            Assert.True(nonGeneric.IsReadOnly);
            Assert.True(nonGeneric.IsFixedSize);
            Assert.Throws<NotSupportedException>(() => nonGeneric[0] = before[1]);
            Assert.Throws<NotSupportedException>(() => nonGeneric.Add(before[0]));
            Assert.Equal(before, list);
            Assert.Equal(typeof(ReadOnlyCollection<VisibleSymbol>), list.GetType());
        }

        var sibling = model.ScopeVisibilities.Last();
        Assert.Equal(scope.Symbols.Count, scope.Symbols.ToArray().Length);
        Assert.NotNull(sibling.Symbols);
    }

    /// <summary>
    /// Every read operation of the shared view agrees with an array-backed list of the same
    /// elements: indexing (with out-of-range rejection), IndexOf and Contains (by record equality,
    /// value-equal probes included), CopyTo at an offset (with its argument checks), and the
    /// non-generic views.
    /// </summary>
    [Fact]
    public void ReadOperations_AgreeWithAnArrayBackedList()
    {
        var model = Model(Library("Lib", 5) + Siblings(3, 12, i => $"    open Lib\n    Y{i} = {i}\n    Y{i}\n"));
        foreach (var scope in model.ScopeVisibilities.Where(candidate => candidate.View is not null))
        {
            var list = scope.Symbols;
            var array = list.ToArray();
            IList<VisibleSymbol> reference = Array.AsReadOnly(array);
            var generic = (IList<VisibleSymbol>)list;
            Assert.Throws<ArgumentOutOfRangeException>(() => list[-1]);
            Assert.Throws<ArgumentOutOfRangeException>(() => list[array.Length]);
            foreach (var symbol in array)
            {
                Assert.Equal(reference.IndexOf(symbol), generic.IndexOf(symbol));
                Assert.True(generic.Contains(symbol));
                var valueEqual = new VisibleSymbol(symbol.Name, symbol.Classification, symbol.Declaration, symbol.Property, symbol.Members.Count == 0 ? null : symbol.Members);
                Assert.Equal(reference.IndexOf(valueEqual), generic.IndexOf(valueEqual));
                var other = new VisibleSymbol(
                    symbol.Name,
                    symbol.Classification == IdentifierClassification.Builtin ? IdentifierClassification.Unresolved : IdentifierClassification.Builtin,
                    symbol.Declaration,
                    symbol.Property);
                Assert.Equal(-1, generic.IndexOf(other));
                Assert.False(generic.Contains(other));
            }

            Assert.Equal(-1, generic.IndexOf(null!));
            Assert.False(generic.Contains(null!));
            var target = new VisibleSymbol[array.Length + 3];
            generic.CopyTo(target, 2);
            Assert.Equal(array, target.Skip(2).Take(array.Length));
            Assert.Throws<ArgumentNullException>(() => generic.CopyTo(null!, 0));
            Assert.ThrowsAny<ArgumentException>(() => generic.CopyTo(new VisibleSymbol[array.Length], 1));
            Assert.ThrowsAny<ArgumentException>(() => generic.CopyTo(target, -1));
            var objects = new object[array.Length];
            ((ICollection)list).CopyTo(objects, 0);
            Assert.Equal(array, objects);
            Assert.Equal(array.Length, ((ICollection)list).Count);
        }
    }

    /// <summary>
    /// A retained scope list references nothing but public semantic values and its own immutable
    /// storage: no AST node, lexical frame, symbol table, interner, or builder is reachable, so
    /// retaining a model (or one scope of it) never retains the analysis that built it.
    /// </summary>
    [Fact]
    public async Task RetainedScopes_ReachNoAnalysisState()
    {
        var modules = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["https://katlang.org/fe4b/lib.kat"] = "public m0 = 1\npublic m1 = 2",
            ["https://katlang.org/fe4b/deferred.kat"] = "public Later = 1",
        };
        var source = "open 'https://katlang.org/fe4b/lib.kat'\nx, y = (1, 2)\nF(0) = {\n    open 'https://katlang.org/fe4b/deferred.kat'\n    B = {\n        X = 1\n        X + m0\n    }\n    B\n}\nF(n) = m0\nF(1)";
        var options = new RunOptions { DownloadCode = (url, _) => ValueTask.FromResult(modules[url]), AllowedHosts = ["katlang.org"] };
        var parsed = (await SourceProvenance.ParseValidAsync(source, options)).Parsed;
        var model = SemanticModelBuilder.Build(parsed);
        Assert.Contains(model.ScopeVisibilities, scope => scope.View is { DeferredLevels: > 0 });

        var allowed = new HashSet<Type>
        {
            typeof(ScopeVisibility), typeof(ScopeSymbolView), typeof(VisibilityNode), typeof(VisibleSymbol),
            typeof(DeclarationOccurrence), typeof(PropertyInfo), typeof(PropertySignatureInfo), typeof(PropertyParameterInfo),
            typeof(ConditionalBranchInfo), typeof(PropertyAliasTargetInfo), typeof(ReadOnlyCollection<VisibleSymbol>),
        };
        var seen = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<object>(model.ScopeVisibilities);
        while (pending.TryPop(out var item))
        {
            var type = item.GetType();
            if (type == typeof(string) || type.IsPrimitive || type.IsEnum || !seen.Add(item))
                continue;
            if (item is Array array)
            {
                foreach (var element in array)
                    if (element is not null) pending.Push(element);
                continue;
            }

            if (type.IsValueType)
                continue;

            var immutableSet = type.Namespace == "System.Collections.Immutable";
            var collection = type.Namespace == "System.Collections.ObjectModel" && type.IsGenericType;
            var comparer = typeof(IEqualityComparer<string>).IsAssignableFrom(type) || type.Name.Contains("Comparer", StringComparison.Ordinal);
            Assert.True(allowed.Contains(type) || immutableSet || collection || comparer, $"A retained scope reaches {type.FullName}.");
            for (var current = type; current is not null; current = current.BaseType)
            {
                foreach (var field in current.GetFields(System.Reflection.BindingFlags.Instance | System.Reflection.BindingFlags.Public | System.Reflection.BindingFlags.NonPublic | System.Reflection.BindingFlags.DeclaredOnly))
                {
                    if (!field.FieldType.IsPointer && field.GetValue(item) is { } value)
                        pending.Push(value);
                }
            }
        }
    }

    /// <summary>
    /// Retaining one scope retains its own tree (and the ancestors' nodes it shares) but not its
    /// siblings' private nodes: once only one block's scope is held, another block's local entry
    /// becomes collectable. Two builds never share storage.
    /// </summary>
    [Fact]
    public void RetainingOneScope_DoesNotRetainItsSiblings()
    {
        var (kept, siblingNode) = BuildAndKeepOneScope();
        GC.Collect();
        GC.WaitForPendingFinalizers();
        GC.Collect();
        Assert.False(siblingNode.IsAlive);
        Assert.Equal("Q", kept.View!.Find("Q")!.Name);

        var first = Model(Blocks(3, 3)).ScopeVisibilities.Last(scope => scope.View is not null).View!;
        var second = Model(Blocks(3, 3)).ScopeVisibilities.Last(scope => scope.View is not null).View!;
        Assert.NotSame(first.Root, second.Root);
    }

    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private static (ScopeVisibility Kept, WeakReference SiblingNode) BuildAndKeepOneScope()
    {
        var model = Model(Blocks(4, 16));
        var blocks = model.ScopeVisibilities.Where(scope => scope.View?.Find("Q") is not null).DistinctBy(scope => scope.View, ReferenceEqualityComparer.Instance).ToList();
        Assert.True(blocks.Count >= 2);
        var siblingPath = FindPath(blocks[1].View!.Root!, "Q");
        var keptNodes = new HashSet<object>(Collect(blocks[0].View!.Root!), ReferenceEqualityComparer.Instance);
        var privateNode = siblingPath.First(node => !keptNodes.Contains(node));
        return (blocks[0], new WeakReference(privateNode));
    }

    private static List<VisibilityNode> FindPath(VisibilityNode root, string name)
    {
        var path = new List<VisibilityNode>();
        for (var node = root; node is not null; node = string.CompareOrdinal(name, node.Name) < 0 ? node.Left : node.Right)
        {
            path.Add(node);
            if (node.Name == name)
                break;
        }

        return path;
    }

    private static IEnumerable<VisibilityNode> Collect(VisibilityNode root) => VisibilityTree.InOrder(root);

    /// <summary>Many threads reading one model's shared views observe identical contents in identical order.</summary>
    [Fact]
    public void SharedViews_ReadConcurrently_AreStable()
    {
        var model = Model(Blocks(64, 64));
        var expected = model.ScopeVisibilities.Select(scope => scope.Symbols.ToArray()).ToArray();
        var completions = model.ScopeVisibilities.Select(scope => model.GetVisibleSymbolsAt(scope.Span?.Start ?? new SourcePosition(1, 1)).ToArray()).ToArray();
        var failures = new ConcurrentBag<string>();
        Parallel.For(0, 32, new ParallelOptions { MaxDegreeOfParallelism = 16 }, worker =>
        {
            for (var round = 0; round < 40; round++)
            {
                var index = (worker * 7 + round) % expected.Length;
                var scope = model.ScopeVisibilities[index];
                var symbols = scope.Symbols;
                if (!symbols.SequenceEqual(expected[index]) || (symbols.Count > 0 && !ReferenceEquals(symbols[round % symbols.Count], expected[index][round % symbols.Count])))
                    failures.Add($"scope {worker}/{round}");
                if (!model.GetVisibleSymbolsAt(scope.Span?.Start ?? new SourcePosition(1, 1)).SequenceEqual(completions[index]))
                    failures.Add($"completion {worker}/{round}");
            }
        });
        Assert.Empty(failures);
    }

    /// <summary>
    /// Queries read the shared storage in place: completion over a 2,000-name scope allocates only
    /// its small prelude-difference array and wrappers (the former merge copied the scope and built
    /// a name set per call), and enumerating a scope allocates only its traversal stack.
    /// </summary>
    [Fact]
    public void Queries_AllocateIndependentlyOfTheScopeWidth()
    {
        var model = Model(Canonical(1000, 1000));
        var scope = model.ScopeVisibilities.First(candidate => candidate.Symbols.Count > 1000);
        var position = scope.Span!.Value.Start;
        _ = model.GetVisibleSymbolsAt(position);
        var before = GC.GetAllocatedBytesForCurrentThread();
        var merged = model.GetVisibleSymbolsAt(position);
        var completionAllocation = GC.GetAllocatedBytesForCurrentThread() - before;
        Assert.True(merged.Count > 2000);
        Assert.InRange(completionAllocation, 0, 8 * 1024);

        var count = 0;
        before = GC.GetAllocatedBytesForCurrentThread();
        foreach (var symbol in scope.Symbols)
            count += symbol.Name.Length > 0 ? 1 : 0;
        var enumerationAllocation = GC.GetAllocatedBytesForCurrentThread() - before;
        Assert.Equal(scope.Symbols.Count, count);
        Assert.InRange(enumerationAllocation, 0, 1024);
    }

    /// <summary>
    /// Completion stays complete for a wide hostile scope: the first, a middle, and the last base
    /// name, the block's own local and shadow, a root name, an opened name, and the unshadowed
    /// prelude are all offered once, in order.
    /// </summary>
    [Fact]
    public void WideCompletion_IsComplete()
    {
        const int width = 300;
        var source = Library("Lib", 4) + string.Concat(Enumerable.Range(0, width).Select(i => $"A{i} = {i}\n"))
            + "B = {\n    open Lib\n    A150 = 5\n    Local = 1\n    Local + A150\n}\n1";
        var model = Model(source);
        var block = model.ScopeVisibilities.Where(scope => scope.View?.Find("Local") is not null).MinBy(scope => scope.NestingDepth)!;
        var merged = model.GetVisibleSymbolsAt(block.Span!.Value.Start);
        var names = merged.Select(symbol => symbol.Name).ToList();
        Assert.Equal(names.Count, names.Distinct(StringComparer.Ordinal).Count());
        foreach (var name in new[] { "A0", "A150", "A299", "Local", "B", "Lib", "m0", "m3", "sum", "if", "Math" })
            Assert.Contains(name, names);
        Assert.Equal(width + 4 + 3 + PreludeCatalog.Symbols.Count, merged.Count);
        var root = Assert.Single(model.ScopeVisibilities, scope => scope.Span is null);
        var shadow = merged.Single(symbol => symbol.Name == "A150");
        Assert.NotSame(root.View!.Find("A150"), shadow);
        Assert.True(shadow.Declaration!.Span.Start.Line > width);
        Assert.Same(root.View.Find("A0"), merged.Single(symbol => symbol.Name == "A0"));
        Assert.Equal(IdentifierClassification.PropertyReference, merged.Single(symbol => symbol.Name == "m3").Classification);
    }
}
