using System.Reflection;
using SignatureMap = KatLang.ImplicitArgumentResolver.SignatureMap;
using SummarySeed = KatLang.PropertyDependencyGraphBuilder.SummarySeed;
using VisibleProperty = KatLang.ImplicitArgumentResolver.VisibleProperty;

namespace KatLang.Tests;

/// <summary>
/// SEC-S1 (October 2026): deterministic pins for the front-end memory representation repairs.
/// Each test measures the PHYSICAL objects a pass keeps reachable — never wall-clock time or
/// process memory — and the measured failure mode is the one the repair removed: a signature-map
/// version chain that retained every superseded immutable dictionary (O(P log P) nodes for P
/// writes), summary seeds that allocated four empty collections each, absorbed-part sets for
/// single-part seeds, and a collision-validator set per visited node. Behavior around every
/// repaired path is pinned too: equal projections, equal seed content, and per-context
/// validation of a shared node. The process-level measurement lives in the
/// <c>fe-mem</c> probe (<c>fuzz/KatLang.ParserFuzz</c>, see <c>fuzz/README.md</c>).
/// </summary>
public class FrontEndMemoryRepresentationTests
{
    private static VisibleProperty Entry(Algorithm value) => new(CallableSignature.FromAlgorithm("P", value), value);

    private static Algorithm Leaf() => new Algorithm.User(null, [], [], [], OutputBundle.Empty);

    /// <summary>
    /// A level of P properties writes its map P times. Every write path-copies the persistent
    /// dictionary, and the version chain used to keep each version's dictionary — about P·log P
    /// nodes. Now a version records only its changes, so the map reaches its CURRENT dictionary's
    /// nodes alone (one per distinct name hash): linear in P, whatever the history.
    /// </summary>
    [Fact]
    public void SignatureMap_VersionChain_RetainsOnlyTheCurrentDictionary()
    {
        const int writes = 2048;
        var map = SignatureMap.Empty(observations: null);
        var leaf = Leaf();
        for (var i = 0; i < writes; i++)
            map.Set($"n{i}", Entry(leaf));

        var census = ObjectCensus.Of(map);
        var dictionaryNodes = census.CountWhere(type => type.Name.StartsWith("SortedInt32KeyNode", StringComparison.Ordinal));

        Assert.InRange(dictionaryNodes, writes / 2, 2 * writes);
        // The change records stay (the projection walk replays them), one version per write.
        Assert.Equal(writes + 1, census.CountWhere(type => type == typeof(ImplicitArgumentResolver.SignatureVersion)));
    }

    /// <summary>
    /// The projection of a map's current entries onto a body's free names is the same set whatever
    /// path the cached walk takes: replayed deltas, a direct probe at an ANCESTOR version (whose
    /// entries are recovered from the current ones through the walked changes), or the root.
    /// Oracle: the same footprints' projection of a FLAT copy of the current entries, which probes
    /// the current dictionary directly with nothing to undo. A seeded random history overwrites a
    /// small name universe repeatedly, so ancestor probes see names changed on the walked path.
    /// </summary>
    [Fact]
    public void SignatureFootprints_EveryWalkPath_EqualsTheDirectProjectionOfCurrentEntries()
    {
        var random = new Random(20261023);
        string[] universe = ["a", "b", "c", "d", "e", "f"];
        var values = Enumerable.Range(0, 5).Select(_ => Entry(Leaf())).ToArray();
        var names = new NameSetInterner();
        var footprints = new ImplicitArgumentResolver.SignatureFootprints();
        var maps = new List<SignatureMap> { SignatureMap.Empty(observations: null) };
        var compared = 0;

        for (var step = 0; step < 4000; step++)
        {
            var map = maps[random.Next(maps.Count)];
            switch (random.Next(4))
            {
                case 0:
                    var locals = new Dictionary<string, VisibleProperty>(StringComparer.Ordinal);
                    foreach (var name in universe.Where(_ => random.Next(3) == 0))
                        locals[name] = values[random.Next(values.Length)];
                    maps.Add(map.Extend(locals));
                    break;
                case 1:
                case 2:
                    map.Set(universe[random.Next(universe.Length)], values[random.Next(values.Length)]);
                    break;
                default:
                    var free = names.With(NameSetInterner.Empty, universe.Where(_ => random.Next(2) == 0));
                    var walked = footprints.Capture(free, names, map, observations: null);
                    Assert.Equal(walked, footprints.Capture(free, names, Flat(map, universe, free.Count), observations: null));
                    compared++;
                    break;
            }
        }

        Assert.True(compared > 500);
    }

    private static Dictionary<string, VisibleProperty> CurrentEntries(SignatureMap map, IEnumerable<string> universe)
    {
        var entries = new Dictionary<string, VisibleProperty>(StringComparer.Ordinal);
        foreach (var name in universe)
        {
            if (map.TryGetValue(name, out var entry))
                entries[name] = entry;
        }

        return entries;
    }

    // The current entries plus enough unrelated names that the flat version's delta exceeds any
    // query budget: the projection is then the direct probe of the flat dictionary.
    private static SignatureMap Flat(SignatureMap map, IEnumerable<string> universe, int budget)
    {
        var entries = CurrentEntries(map, universe);
        var padding = Entry(Leaf());
        for (var i = 0; i <= budget; i++)
            entries[$"pad{i}"] = padding;
        return SignatureMap.Empty(observations: null).Extend(entries);
    }

    /// <summary>
    /// The exposure pass keeps one completed summary per distinct algorithm for the whole
    /// resolution. A program of P constant properties requires, references, and qualifies
    /// nothing, so its completed summaries hold no collection at all — formerly every seed
    /// allocated four empty ones and every property-less algorithm an empty member map.
    /// </summary>
    [Fact]
    public void ExposureSummaries_OfAConstantProgram_MaterializeNoEmptyCollections()
    {
        const int properties = 300;
        var source = string.Concat(Enumerable.Range(0, properties).Select(i => $"A{i} = {i}\n")) + "A0";
        var root = SourceProvenance.ParseValid(source).Root;
        var memo = new PropertyDependencyGraphBuilder.SummaryMemo();

        var graph = PropertyDependencyGraphBuilder.BuildSummaries(root, memo);

        Assert.Equal(properties, graph.Count);
        var census = ObjectCensus.Of(memo);
        Assert.Equal(0, census.CountWhere(type => type.IsGenericType && type.GetGenericTypeDefinition() == typeof(HashSet<>)));
        Assert.Equal(0, census.CountWhere(type => type == typeof(PendingReferenceSet)));
        // The one shared empty member map, not one per algorithm.
        Assert.InRange(census.CountWhere(type => type == typeof(Dictionary<string, SummarySeed>)), 0, 2);
        Assert.InRange(census.CountWhere(type => type == typeof(SummarySeed)), properties, properties + 4);
    }

    /// <summary>A missing set reads as the empty set everywhere: equality, emptiness, and content keys agree with materialized empty sets.</summary>
    [Fact]
    public void SummarySeed_LazySetsAndMaterializedEmptySets_HaveIdenticalContent()
    {
        var lazy = new SummarySeed();
        var materialized = new SummarySeed();
        _ = materialized.RequiredAncestorOwnedParameterNames;
        _ = materialized.VisiblePropertyDependencyNames;
        _ = materialized.PendingReferences;
        _ = materialized.OwnerQualifiedParameters;

        Assert.True(lazy.StructurallyEquals(materialized));
        Assert.True(materialized.StructurallyEquals(lazy));
        Assert.True(lazy.SetEquals(materialized));
        Assert.True(lazy.IsEmptyWithoutFolding());
        Assert.True(materialized.IsEmptyWithoutFolding());
        Assert.True(lazy.IsEmpty);
        Assert.Equal(materialized.ContentKey, lazy.ContentKey);

        var named = new SummarySeed(["p"]);
        Assert.False(lazy.StructurallyEquals(named));
        Assert.False(named.StructurallyEquals(materialized));
        var copy = new SummarySeed();
        copy.UnionWith(named);
        Assert.Equal(["p"], copy.RequiredAncestorOwnedParameterNames);
        Assert.True(copy.StructurallyEquals(named));
        // A clone of an empty seed stays empty and independent.
        var clone = lazy.Clone();
        clone.VisiblePropertyDependencyNames.Add("V");
        Assert.True(lazy.IsEmpty);
        Assert.False(clone.IsEmpty);
    }

    /// <summary>
    /// Absorbed completed parts are deduplicated by reference whether the seed scans a short list
    /// or keeps a set past <c>AbsorbedScanLimit</c>; equality compares the parts as a set, and
    /// folding unions every distinct part once.
    /// </summary>
    [Theory]
    [InlineData(3)]
    [InlineData(8)]
    [InlineData(9)]
    [InlineData(20)]
    public void SummarySeed_AbsorbedParts_DeduplicateByReferenceAtEverySize(int parts)
    {
        // Each part carries more entries than an edge copies, so it is absorbed by reference.
        var completed = Enumerable.Range(0, parts)
            .Select(i => new SummarySeed(Enumerable.Range(0, SummarySeed.CopiedCompletedEntries + 1).Select(j => $"p{i}_{j}")))
            .ToArray();
        var forward = new SummarySeed();
        var backward = new SummarySeed();
        foreach (var part in completed.Concat(completed))
            forward.AbsorbCompleted(part);
        foreach (var part in completed.Reverse())
            backward.AbsorbCompleted(part);

        // Only a list longer than the scan limit keeps a reference set beside it (counted before
        // any read folds the parts in).
        Assert.Equal(parts > 8 ? 1 : 0, ObjectCensus.Of(forward).CountWhere(type => type == typeof(HashSet<SummarySeed>)));
        Assert.True(forward.StructurallyEquals(backward));
        Assert.True(backward.StructurallyEquals(forward));
        var fewer = new SummarySeed();
        foreach (var part in completed.Skip(1))
            fewer.AbsorbCompleted(part);
        Assert.False(forward.StructurallyEquals(fewer));
        Assert.Equal(parts * (SummarySeed.CopiedCompletedEntries + 1), forward.RequiredAncestorOwnedParameterNames.Count);
        Assert.True(forward.SetEquals(backward));
    }

    /// <summary>
    /// The collision validator visits a node once per distinct visible-parameter context. A node
    /// reached in ONE context keeps only that context id inline: no per-node set. A node SHARED
    /// by two owners is validated in each of their contexts, whichever is reached first — the
    /// declaration conflicts with only one owner's parameter, and is reported exactly once.
    /// </summary>
    [Fact]
    public void CollisionValidator_SingleContextNodes_KeepNoSets_AndSharedNodesValidateEveryContext()
    {
        const int properties = 300;
        var dense = SourceProvenance.ParseValid(
            string.Concat(Enumerable.Range(0, properties).Select(i => $"F{i}(x) = x + {i}\n")) + "F0(1)").Root;
        var validator = new ParameterPropertyCollisionValidator(new DiagnosticBag(), programRoot: dense);
        validator.VisitAlgorithm(dense);
        var census = ObjectCensus.Of(validator);
        Assert.Equal(0, census.CountWhere(type => type == typeof(HashSet<int>)));

        // The block is an operand, so it is a nested algorithm of G's output (a whole-value block
        // would BE G's body).
        var parsed = SourceProvenance.ParseValid("F(x) = x\nG(y) = y + {\n    x = 1\n    x\n}\n1").Root;
        var f = Assert.IsType<Algorithm.User>(parsed.Properties.Single(p => p.Name == "F").Value);
        var g = Assert.IsType<Algorithm.User>(parsed.Properties.Single(p => p.Name == "G").Value);
        // F now outputs G's very block: the block's `x` collides with F's parameter, not G's.
        var sharedF = f with { Output = g.Output };
        foreach (var order in new[] { new[] { "G", "F" }, ["F", "G"] })
        {
            var properties2 = order.Select(name => name == "F"
                ? parsed.Properties.Single(p => p.Name == "F") with { Value = sharedF }
                : parsed.Properties.Single(p => p.Name == "G")).ToList();
            var root = parsed with { Properties = properties2 };
            var diagnostics = new DiagnosticBag();
            new ParameterPropertyCollisionValidator(diagnostics, programRoot: root).VisitAlgorithm(root);
            Assert.Single(diagnostics, d => d.Code == DiagnosticCode.ParameterPropertyCollision);
        }
    }

    /// <summary>
    /// Physical HEAP objects reachable from a root through instance fields and array elements —
    /// struct fields and struct array elements (dictionary entries, buckets) included, since they
    /// hold references inline — each heap object counted once by reference: the shared-DAG view of
    /// what a structure keeps alive. Strings, delegates, and reflection objects are leaves.
    /// </summary>
    private sealed class ObjectCensus
    {
        private readonly Dictionary<Type, int> _counts = [];

        public int CountWhere(Func<Type, bool> predicate) => _counts.Where(pair => predicate(pair.Key)).Sum(pair => pair.Value);

        public static ObjectCensus Of(object root)
        {
            var census = new ObjectCensus();
            var seen = new HashSet<object>(ReferenceEqualityComparer.Instance);
            var pending = new Stack<object>();
            pending.Push(root);
            while (pending.TryPop(out var node))
            {
                if (!seen.Add(node))
                    continue;
                var type = node.GetType();
                census._counts[type] = census._counts.GetValueOrDefault(type) + 1;
                if (node is string || node is Delegate || node is MemberInfo || node is Assembly)
                    continue;
                if (node is Array array)
                {
                    var element = type.GetElementType()!;
                    if (!element.IsPrimitive && !element.IsEnum && !element.IsPointer)
                    {
                        foreach (var item in array)
                            PushReferences(item, pending);
                    }

                    continue;
                }

                PushFields(node, type, pending);
            }

            return census;
        }

        // A reference is a reachable heap object; a struct value is walked in place.
        private static void PushReferences(object? value, Stack<object> pending)
        {
            if (value is null)
                return;
            var type = value.GetType();
            if (!type.IsValueType)
                pending.Push(value);
            else if (!type.IsPrimitive && !type.IsEnum)
                PushFields(value, type, pending);
        }

        private static void PushFields(object node, Type type, Stack<object> pending)
        {
            for (var current = type; current is not null && current != typeof(object) && current != typeof(ValueType); current = current.BaseType)
            {
                foreach (var field in current.GetFields(BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.DeclaredOnly))
                {
                    if (field.FieldType.IsPrimitive || field.FieldType.IsEnum || field.FieldType.IsPointer)
                        continue;
                    PushReferences(field.GetValue(node), pending);
                }
            }
        }
    }
}
