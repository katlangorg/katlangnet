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

    /// <summary>
    /// The hash-aware attack of issue #169: names ordered by THIS process's string hashes (the
    /// longest monotone hash run among <paramref name="candidates"/> names), which built a chain
    /// as deep as the selection while priorities were <see cref="string.GetHashCode()"/>.
    /// </summary>
    private static string[] HashMonotoneNames(int candidates)
    {
        var names = Enumerable.Range(0, candidates).Select(i => $"common_prefix_{i:D5}").ToArray();
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
        return (up.Length > down.Length ? up : down).Select(i => names[i]).ToArray();
    }

    /// <summary>
    /// Production priorities are private per-builder random draws (SCOPE-BAL-2), so knowing this
    /// process's string hashes no longer selects the tree shape. The selection from 65,536
    /// candidates is ~512 names long (a monotone run of n random values is ~2√n); the old
    /// priorities made exactly that chain. The bound 64 is not a balance proof: a random treap of
    /// n ≤ 600 nodes has expected depth ≈ 4.3 ln n ≈ 27, and the expected number of nodes at depth
    /// 64 is at most (2 H_n)^64 / 64! &lt; 10⁻¹⁵ in the ideal random-priority model, leaving a
    /// wide margin for height variation. Finite random samples are not a deterministic guarantee.
    /// </summary>
    [Fact]
    public void HashAwareHost_NoLongerSelectsTheTreeShape()
    {
        var selected = HashMonotoneNames(65_536);
        Assert.InRange(selected.Length, 400, 600);
        var trees = new VisibilityTreeBuilder(null);
        var entries = selected.Select(name => trees.Entry(new VisibleSymbol(name, IdentifierClassification.PropertyReference, null, null), 0, null)).ToList();
        var root = trees.Build(entries)!;
        var scope = new ScopeVisibility(null, new ScopeSymbolView(root, 0, null), 0);
        var depth = ScopeVisibilityCensus.Measure([scope]).MaxTreeDepth;
        Assert.InRange(depth, 1, 64);
        Assert.Equal(entries.Select(e => e.Name), scope.Symbols.Select(s => s.Name));
        for (var i = 0; i < entries.Count; i++)
        {
            Assert.Same(entries[i].Symbol, scope.View!.Find(entries[i].Name));
            Assert.Equal(i, ((IList<VisibleSymbol>)scope.Symbols).IndexOf(entries[i].Symbol));
            Assert.InRange(ScopeVisibilityCensus.LookupProbes(scope, entries[i].Name), 1, depth);
        }

        // Replacement, removal and reinsertion stay correct and canonical in the builder.
        var middle = entries[entries.Count / 2];
        Assert.Same(root, trees.Set(root, middle));
        var replacement = trees.Entry(new VisibleSymbol(middle.Name, IdentifierClassification.PropertyReference, null, null), 0, null);
        Assert.Equal(middle.Priority, replacement.Priority);
        var replaced = trees.Set(root, replacement);
        Assert.Same(replacement.Symbol, VisibilityTree.Find(replaced, middle.Name)!.Symbol);
        Assert.Same(root, trees.Set(replaced, middle));
        var removed = trees.Remove(root, middle.Name);
        Assert.Equal(entries.Count - 1, removed!.Count);
        Assert.Null(VisibilityTree.Find(removed, middle.Name));
        Assert.Same(root, trees.Set(removed, middle));
        Assert.Same(root, trees.Build(entries));
    }

    /// <summary>
    /// The public path (Parser.Parse → SemanticModelBuilder.Build) uses the same private
    /// priorities: a document declaring the hash-selected names in hash order — a ~512-deep chain
    /// under the old priorities — has shallow scopes, matching the eager oracle. Sibling blocks
    /// also exercise the incremental updates that amplified the old attack.
    /// </summary>
    [Theory]
    [InlineData(0)]
    [InlineData(24)]
    public void HashAwareSource_BuildsAShallowModelThroughThePublicPath(int blocks)
    {
        var selected = HashMonotoneNames(65_536);
        Assert.InRange(selected.Length, 400, 600);
        var blockNames = Enumerable.Range(0, blocks).Select(i => $"Block{i:D2}").ToArray();
        var source = string.Concat(selected.Select((name, i) => $"{name} = {i}\n"))
            + string.Concat(blockNames.Select((name, i) => $"{name} = {{ zzlocal{i:D2} = 1\nzzlocal{i:D2} }}\n")) + "1";
        var parsed = SourceProvenance.ParseValid(source).Parsed;
        var (model, eager) = SemanticModelBuilder.BuildWithEagerVisibilityReference(parsed);
        Assert.InRange(ScopeVisibilityCensus.Measure(model.ScopeVisibilities).MaxTreeDepth, 1, 64);
        Assert.Equal(model.ScopeVisibilities.Count, eager.Count);
        for (var i = 0; i < eager.Count; i++)
            Assert.Equal(Content(eager[i]), Content(model.ScopeVisibilities[i].Symbols));
        var publicModel = SemanticModelBuilder.Build(parsed);
        Assert.InRange(ScopeVisibilityCensus.Measure(publicModel.ScopeVisibilities).MaxTreeDepth, 1, 64);
        Assert.Equal(selected.Concat(blockNames).Order(StringComparer.Ordinal), publicModel.ScopeVisibilities[0].Symbols.Select(s => s.Name));
    }

    /// <summary>
    /// A name's priority belongs to the name within ONE builder: every symbol, meta and twin of
    /// it, before and after removal, gets the first draw. Builders draw independently — not one
    /// shared mapping, and not the process string hash (individual collisions are possible, all
    /// 256 agreeing is not).
    /// </summary>
    [Fact]
    public void Priorities_AreStablePerNameAndPrivatePerBuilder()
    {
        var names = Enumerable.Range(0, 256).Select(i => $"n{i}").ToArray();
        var first = new VisibilityTreeBuilder(null);
        var second = new VisibilityTreeBuilder(null);
        var firstPriorities = names.Select(first.PriorityOf).ToArray();
        var secondPriorities = names.Reverse().Select(second.PriorityOf).Reverse().ToArray();
        Assert.Equal(firstPriorities, names.Select(first.PriorityOf));
        Assert.True(firstPriorities.Zip(secondPriorities).Count(pair => pair.First == pair.Second) < 8);
        Assert.True(firstPriorities.Zip(names).Count(pair => pair.First == pair.Second.GetHashCode()) < 8);
        Assert.True(firstPriorities.Distinct().Count() > 240);

        var name = names[3];
        var direct = new VisibleSymbol(name, IdentifierClassification.PropertyReference, null, null);
        var parameter = new VisibleSymbol(name, IdentifierClassification.ExplicitParameterReference, null, null);
        var twin = new VisibleSymbol(name, IdentifierClassification.DeferredModuleReference, null, null);
        var entries = new[]
        {
            first.Entry(direct, VisibilityEntry.DirectMeta, null),
            first.Entry(parameter, VisibilityEntry.DirectMeta, null),
            first.Entry(direct, VisibilityEntry.OpenMeta(0), twin),
            first.Entry(direct, VisibilityEntry.OpenMeta(3), null),
        };
        Assert.All(entries, entry => Assert.Equal(firstPriorities[3], entry.Priority));
        var root = first.Set(null, entries[0]);
        Assert.Null(first.Remove(root, name));
        Assert.Equal(firstPriorities[3], first.Entry(direct, VisibilityEntry.DirectMeta, null).Priority);
        Assert.Same(root, first.Set(null, entries[0]));
    }

    /// <summary>
    /// Independently randomized builds of one document, run in parallel, agree on every scope's
    /// visible content (names, classifications, declarations, properties) and each matches its own
    /// eager oracle; their trees need not share a shape.
    /// </summary>
    [Fact]
    public void IndependentBuilds_AgreeOnContentUnderDifferentPriorities()
    {
        var source = "Lib = { public A = 1\npublic B = 2\npublic C(x) = x\n1 }\nOther = { public B = 3\n1 }\n"
            + "U(p, q) = { open Lib, Other\n" + string.Concat(Enumerable.Range(0, 40).Select(i => $"L{i} = {{ v{i} = p\nA = q\nv{i} }}\n")) + "A + C(p) }\nU(1, 2)";
        var parsed = SourceProvenance.ParseValid(source).Parsed;
        var builds = new (SemanticModel Model, IReadOnlyList<IReadOnlyList<VisibleSymbol>> Eager)[8];
        Parallel.For(0, builds.Length, i => builds[i] = SemanticModelBuilder.BuildWithEagerVisibilityReference(parsed));
        var reference = builds[0].Model.ScopeVisibilities;
        foreach (var (model, eager) in builds)
        {
            Assert.Equal(reference.Count, model.ScopeVisibilities.Count);
            for (var s = 0; s < reference.Count; s++)
            {
                var actual = model.ScopeVisibilities[s].Symbols;
                Assert.Equal(Content(eager[s]), Content(actual));
                Assert.Equal(
                    reference[s].Symbols.Select(x => (x.Name, x.Classification, x.Declaration?.Span, x.Property?.Name)),
                    actual.Select(x => (x.Name, x.Classification, x.Declaration?.Span, x.Property?.Name)));
            }
        }
    }

    /// <summary>A priority override must be a function of the name: a second, different answer fails loudly.</summary>
    [Fact]
    public void InconsistentPriorityOverride_FailsInsteadOfCorruptingTheHeapOrder()
    {
        var next = 0;
        var trees = new VisibilityTreeBuilder(null) { PriorityOverride = _ => next++ };
        var symbol = new VisibleSymbol("x", IdentifierClassification.PropertyReference, null, null);
        _ = trees.Entry(symbol, 0, null);
        Assert.Throws<InvalidOperationException>(() => trees.Entry(symbol, 0, null));

        var constant = new VisibilityTreeBuilder(null) { PriorityOverride = _ => 5 };
        Assert.Equal(5, constant.Entry(symbol, 0, null).Priority);
        Assert.Equal(5, constant.Entry(symbol, 1, null).Priority);
    }

    [Fact]
    public void FailedPriorityOverride_DoesNotRecordAPlaceholder()
    {
        var fail = true;
        var trees = new VisibilityTreeBuilder(null)
        {
            PriorityOverride = _ => fail ? throw new InvalidOperationException("test draw failed") : 42,
        };
        var symbol = new VisibleSymbol("x", IdentifierClassification.PropertyReference, null, null);
        Assert.Throws<InvalidOperationException>(() => trees.Entry(symbol, 0, null));
        fail = false;
        Assert.Equal(42, trees.Entry(symbol, 0, null).Priority);
        Assert.Equal(42, trees.Entry(symbol, 1, null).Priority);
    }

#if DEBUG
    /// <summary>
    /// Interning keys omit the priority, so a node of one builder must never carry another
    /// builder's priority: in Debug builds <see cref="VisibilityTreeBuilder.Make"/> rejects an
    /// entry whose priority is not this builder's for its name.
    /// </summary>
    [Fact]
    public void ForeignPriorityEntries_AreRejectedByTheDebugInternCheck()
    {
        var symbol = new VisibleSymbol("x", IdentifierClassification.PropertyReference, null, null);
        var own = new VisibilityTreeBuilder(null) { PriorityOverride = _ => 1 };
        var foreign = new VisibilityTreeBuilder(null) { PriorityOverride = _ => 2 };
        var entry = foreign.Entry(symbol, 0, null);
        Assert.Throws<InvalidOperationException>(() => own.Make(entry, null, null));
        _ = own.Entry(symbol, 0, null);
        Assert.Throws<InvalidOperationException>(() => own.Set(null, entry));
        var node = own.Make(own.Entry(symbol, 0, null), null, null);
        Assert.Equal(1, node.Priority);
        // This foreign entry has the SAME NodeKey as the existing node. The guard must run
        // before interning could silently return that node with the wrong requested priority.
        Assert.Throws<InvalidOperationException>(() => own.Make(entry, null, null));
        Assert.Same(node, own.Make(own.Entry(symbol, 0, null), null, null));
    }
#endif

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
        Property[] TieAll(IReadOnlyList<Property> properties) => properties.Select(p => p with
        {
            DeclarationSpans = p.Name is "Z" or "E" ? [span] : p.DeclarationSpans,
            Value = p.Value switch
            {
                Algorithm.User user => Tie(user),
                // M4★: B and D are forwarding carriers, which keep their own declarations.
                Algorithm.Alias alias => alias with { Properties = TieAll(alias.Properties) },
                _ => p.Value,
            },
        }).ToArray();
        Algorithm.User Tie(Algorithm.User algorithm) => algorithm with { Properties = TieAll(algorithm.Properties) };
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

    /// <summary>A scope's visible content by name, classification, and declaration/property/member identity.</summary>
    private static IEnumerable<(string, IdentifierClassification, object?, object?, int)> Content(IEnumerable<VisibleSymbol> symbols)
        => symbols.Select(symbol => (symbol.Name, symbol.Classification, (object?)symbol.Declaration, (object?)symbol.Property, symbol.Members.Count)).ToList();

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
