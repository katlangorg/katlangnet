using KatLang.Semantics;

namespace KatLang.Tests;

public class Fe4bHostileReviewTests
{
    [Fact]
    public void DistinctHostAliases_ShareMemberBackingBehindDistinctWrappers()
    {
        const int width = 256;
        var source = "Lib = {\n" + string.Concat(Enumerable.Range(0, width).Select(i => $"public M{i} = {i}\n")) + "1\n}\n1";
        var parsed = SourceProvenance.ParseValid(source).Parsed;
        var template = Assert.Single(parsed.Root.Properties);
        var root = parsed.Root with { Properties = Enumerable.Range(0, width).Select(i => template with { Name = $"Alias{i}" }).ToArray() };
        var model = SemanticModelBuilder.Build(root);
        var aliases = model.ScopeVisibilities[0].Symbols;
        Assert.Equal(width, aliases.Count);
        var lists = aliases.Select(a => a.Members).ToArray();
        Assert.All(lists, list => Assert.Equal(width, list.Count));
        Assert.Equal(width, lists.Distinct(ReferenceEqualityComparer.Instance).Count());
        var backing = typeof(System.Collections.ObjectModel.ReadOnlyCollection<VisibleSymbol>)
            .GetProperty("Items", System.Reflection.BindingFlags.NonPublic | System.Reflection.BindingFlags.Instance)!;
        var shared = backing.GetValue(lists[0]);
        Assert.All(lists, list => Assert.Same(shared, backing.GetValue(list)));
        Assert.All(lists, list => Assert.Throws<NotSupportedException>(() => ((IList<VisibleSymbol>)list).Clear()));
        // The public constructor continues to snapshot a caller-owned mutable list.
        var input = lists[0].ToList();
        var hostSymbol = new VisibleSymbol("Host", IdentifierClassification.PropertyReference, null, null, input);
        input.Clear();
        Assert.Equal(width, hostSymbol.Members.Count);
    }

    [Theory]
    [InlineData(128)]
    [InlineData(256)]
    public void MetadataRegistration_DoesNotRescanTheSharedVisibleBase(int width)
    {
        var names = string.Join(", ", Enumerable.Range(0, width).Select(i => $"v{i}"));
        var source = $"O({names}) = {{ Base = {names}\n"
            + string.Concat(Enumerable.Range(0, width).Select(i => $"P{i} = {{ Q = Base\nQ }}\n")) + "Base\n}\n1";
        var parsed = SourceProvenance.ParseValid(source).Parsed;
        var observed = new FrontEndTraversalObservations();
        var model = SemanticModelBuilder.Build(parsed, observed);
        Assert.InRange(observed.ScopeVisibilityMetadataEntries, width, 12L * width);
        Assert.True(ScopeVisibilityCensus.Measure(model.ScopeVisibilities).Memberships > 4L * width * width);
    }

    [Fact]
    public void HashAwareHost_CanSelectAnUnbalancedButCorrectTree()
    {
        // Hash randomization protects against a fixed hostile source, not a host that
        // observes this process's hashes and chooses its names adaptively.
        var names = Enumerable.Range(0, 4096).Select(i => $"common_prefix_{i:D5}").ToArray();
        int[] Subsequence(bool increasing)
        {
            var tails = new List<int>();
            var previous = new int[names.Length];
            Array.Fill(previous, -1);
            for (var i = 0; i < names.Length; i++)
            {
                var value = (long)names[i].GetHashCode() * (increasing ? 1 : -1);
                var lo = 0;
                var hi = tails.Count;
                while (lo < hi)
                {
                    var mid = (lo + hi) / 2;
                    if ((long)names[tails[mid]].GetHashCode() * (increasing ? 1 : -1) < value) lo = mid + 1;
                    else hi = mid;
                }
                if (lo > 0) previous[i] = tails[lo - 1];
                if (lo == tails.Count) tails.Add(i); else tails[lo] = i;
            }
            var result = new List<int>();
            for (var i = tails[^1]; i >= 0; i = previous[i]) result.Add(i);
            result.Reverse();
            return result.ToArray();
        }
        var up = Subsequence(true);
        var down = Subsequence(false);
        var selected = up.Length > down.Length ? up : down;
        Assert.True(selected.Length >= 60);
        var trees = new VisibilityTreeBuilder(null);
        var entries = selected.Select(i => trees.Entry(new VisibleSymbol(names[i], IdentifierClassification.PropertyReference, null, null), 0, null)).ToList();
        var root = trees.Build(entries)!;
        var scope = new ScopeVisibility(null, new ScopeSymbolView(root, 0, null), 0);
        Assert.Equal(entries.Count, ScopeVisibilityCensus.Measure([scope]).MaxTreeDepth);
        Assert.Equal(entries.Select(e => e.Name), scope.Symbols.Select(s => s.Name));
        Assert.Same(root, trees.Set(root, entries[entries.Count / 2]));
        var removed = trees.Remove(root, entries[entries.Count / 2].Name);
        Assert.Equal(entries.Count - 1, removed!.Count);
        Assert.Same(root, trees.Set(removed, entries[entries.Count / 2]));
    }

    [Fact]
    public void CensusDepth_IncludesTheFullHeightOfAnAlreadyVisitedSharedSubtree()
    {
        var trees = new VisibilityTreeBuilder(null) { PriorityOverride = _ => 0 };
        var entries = new[] { "c", "d", "e", "f" }.Select(n => trees.Entry(new VisibleSymbol(n, IdentifierClassification.PropertyReference, null, null), 0, null)).ToList();
        var root = trees.Build(entries)!;
        var deeper = trees.Set(root, trees.Entry(new VisibleSymbol("b", IdentifierClassification.PropertyReference, null, null), 0, null));
        var scopes = new[] { new ScopeVisibility(null, new ScopeSymbolView(root, 0, null), 0), new ScopeVisibility(null, new ScopeSymbolView(deeper, 0, null), 1) };
        Assert.Equal(5, ScopeVisibilityCensus.Measure(scopes).MaxTreeDepth);
        Assert.Equal(5, ScopeVisibilityCensus.Measure(scopes.Reverse().ToArray()).MaxTreeDepth);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void EqualSpanDeclarations_KeepTheLiteralBaselineRegistrationOrder(bool opens)
    {
        var source = $"U = {{ {(opens ? "open Lib" : "")}\n A = count([1])\n B = {{ D = {{ E = 2\nE }}\n D }}\n1 }}\nLib = {{ public Z = 1\n1 }}\n1";
        var parsed = SourceProvenance.ParseValid(source).Parsed;
        var span = new SourceSpan(new SourcePosition(100, 1), new SourcePosition(100, 2));
        Algorithm.User Tie(Algorithm.User algorithm) => algorithm with
        {
            Properties = algorithm.Properties.Select(p => p with
            {
                DeclarationSpans = p.Name is "Z" or "E" ? [span] : p.DeclarationSpans,
                Value = p.Value is Algorithm.User user ? Tie(user) : p.Value,
            }).ToArray(),
        };
        var model = SemanticModelBuilder.Build(Tie(parsed.Root));
        Assert.Equal(["Z", "E"], model.Declarations.Where(d => d.Span == span).Select(d => d.Name));
        Assert.Equal("Z", model.FindResolutionAt(span.Start)!.Occurrence.Name);
        Assert.Equal("Z", model.FindPropertyAt(span.Start)!.Name);
        Assert.Equal(2, model.Declarations.Count(d => d.Span == span));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void DeferredTwin_IsPartOfEntryIdentity(bool collide)
    {
        var trees = new VisibilityTreeBuilder(null, collide);
        var symbol = new VisibleSymbol("X", IdentifierClassification.PropertyReference, null, null);
        var twin = new VisibleSymbol("X", IdentifierClassification.DeferredModuleReference, null, null);
        var ordinary = trees.Entry(symbol, VisibilityEntry.OpenMeta(0), null);
        var deferred = trees.Entry(symbol, VisibilityEntry.OpenMeta(0), twin);
        var first = trees.Set(null, ordinary);
        var second = trees.Set(null, deferred);
        Assert.NotSame(first, second);
        Assert.Same(twin, new ScopeSymbolView(second, 1, null).Find("X"));
        Assert.Same(second, trees.Set(first, deferred));
        Assert.Same(first, trees.Set(second, ordinary));
        Assert.Same(second, trees.Apply(first, [VisibilityDelta.Set(deferred)]));
        Assert.Same(first, trees.Apply(second, [VisibilityDelta.Set(ordinary)]));
    }

    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public void DictionaryOracle_CoversPersistentVersionsAndAllEntryDimensions(bool bulk, bool ties)
    {
        var trees = new VisibilityTreeBuilder(null, collideNodeHashes: true) { ForceBulk = bulk, PriorityOverride = ties ? _ => 0 : null };
        string[] names = ["A", "a", "_", "a1", "a10", "a2", "Ä", "é", "e\u0301", "ÿ", "ω", new string('x', 2048)];
        var random = new Random(74023);
        var expected = new Dictionary<string, VisibilityEntry>(StringComparer.Ordinal);
        var versions = new List<(VisibilityNode? Root, Dictionary<string, VisibilityEntry> Expected)>();
        VisibilityNode? root = null;
        for (var step = 0; step < 200; step++)
        {
            var changes = new List<VisibilityDelta>();
            foreach (var name in names.OrderBy(_ => random.Next()).Take(1 + step % names.Length))
            {
                if (random.Next(4) == 0)
                {
                    expected.Remove(name);
                    changes.Add(VisibilityDelta.Remove(name));
                }
                else
                {
                    var symbol = expected.TryGetValue(name, out var old) && random.Next(2) == 0
                        ? old.Symbol : new VisibleSymbol(name, IdentifierClassification.PropertyReference, null, null);
                    var twin = random.Next(2) == 0 ? null : new VisibleSymbol(name, IdentifierClassification.DeferredModuleReference, null, null);
                    var entry = trees.Entry(symbol, random.Next(6), twin);
                    expected[name] = entry;
                    changes.Add(VisibilityDelta.Set(entry));
                }
            }
            root = trees.Apply(root, changes);
            versions.Add((root, new(expected, StringComparer.Ordinal)));
            Check(root, expected);
            var incremental = expected.OrderBy(_ => random.Next()).Aggregate((VisibilityNode?)null, (r, x) => trees.Set(r, x.Value));
            Assert.Same(root, incremental);
            Assert.Same(root, trees.Build(expected.OrderBy(x => x.Key, StringComparer.Ordinal).Select(x => x.Value).ToList()));
        }
        foreach (var version in versions) Check(version.Root, version.Expected);
    }

    private static void Check(VisibilityNode? root, Dictionary<string, VisibilityEntry> expected)
    {
        var ordered = expected.OrderBy(x => x.Key, StringComparer.Ordinal).ToArray();
        Assert.Equal(ordered.Select(x => x.Key), VisibilityTree.InOrder(root).Select(n => n.Name));
        Assert.Equal(ordered.Length, root?.Count ?? 0);
        for (var i = 0; i < ordered.Length; i++)
        {
            var actual = VisibilityTree.Find(root, ordered[i].Key, out var index, out var probes)!;
            Assert.Equal(i, index);
            Assert.InRange(probes, 1, ordered.Length);
            Assert.Same(actual, VisibilityTree.ElementAt(root!, i));
            Assert.Same(ordered[i].Value.Symbol, actual.Symbol);
            Assert.Same(ordered[i].Value.DeferredTwin, actual.DeferredTwin);
            Assert.Equal(ordered[i].Value.Meta, actual.Meta);
        }
        Assert.Null(VisibilityTree.Find(root, "missing"));
    }
}
