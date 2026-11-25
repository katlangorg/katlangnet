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
    /// P nested levels extend their maps P times. Every extension path-copies the persistent
    /// dictionary, and a version chain that kept each version's dictionary would reach about P·log P
    /// nodes. A version records only its changes, so the innermost map reaches its CURRENT
    /// dictionary's nodes alone (one per distinct name hash): linear in P, whatever the history.
    /// (Since B3-5★ no map is written after it is created: extension is the only way a version grows.)
    /// </summary>
    [Fact]
    public void SignatureMap_VersionChain_RetainsOnlyTheCurrentDictionary()
    {
        const int writes = 2048;
        var map = SignatureMap.Empty(observations: null);
        var leaf = Leaf();
        for (var i = 0; i < writes; i++)
            map = map.Extend(new Dictionary<string, VisibleProperty>(StringComparer.Ordinal) { [$"n{i}"] = Entry(leaf) });

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
                    // An overwrite of one name: ancestor probes then see a name changed on the walked path.
                    maps.Add(map.Extend(new Dictionary<string, VisibleProperty>(StringComparer.Ordinal)
                    {
                        [universe[random.Next(universe.Length)]] = values[random.Next(values.Length)],
                    }));
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

        var graph = StandaloneSummaries.Build(root, memo);

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

    // ── Retained empty lists and transient tables (November 2026 follow-up of the B3 memory growth) ──

    private static string RowProgram(int rows)
        => string.Concat(Enumerable.Range(0, rows).Select(i => $"A{i} = {i}\nF{i}(x) = x + {i}\n"))
            + "B = {\n    P = 1\n    P + 0\n}\nA0 + F0(1) + B";

    private static int EmptyScopeLists(Algorithm root)
        => ObjectCensus.Of(root).CountObjects(static node => node is List<Property> { Count: 0 } or List<Expr> { Count: 0 });

    /// <summary>
    /// The elaborated result holds no empty opens or properties list object per body: a body with output rows reads the
    /// shared zero-length arrays for them. Before, every body kept its own empty <see cref="List{T}"/> of each (8.3 MiB
    /// retained on a 2-MiB constant-row source, two per row). The empty lists the result retains no longer grow with the
    /// rows, and the bodies still evaluate. The parameter-pattern list stays the body's own: it is an identity input of
    /// the resolver's signature composition and bundle sharing (FE-3), which a shared empty list would change.
    /// </summary>
    [Fact]
    public void ElaboratedRowBodies_HoldTheSharedEmptyLists_NotOnePerBody()
    {
        var small = SourceProvenance.ParseValid(RowProgram(100)).Root;
        var large = SourceProvenance.ParseValid(RowProgram(200)).Root;

        var retained = EmptyScopeLists(large);
        Assert.True(retained < 10, $"the result retains {retained} empty opens or properties lists");
        Assert.Equal(EmptyScopeLists(small), retained);
        var bodies = large.Properties.Select(property => Assert.IsType<Algorithm.User>(property.Value)).ToArray();
        foreach (var (property, body) in large.Properties.Zip(bodies))
        {
            Assert.Same(Array.Empty<Expr>(), body.Opens);
            if (property.Name != "B")
                Assert.Same(Array.Empty<Property>(), body.Properties);
        }

        Assert.Equal(bodies.Length, bodies.Select(body => body.ParameterPatterns).Distinct(ReferenceEqualityComparer.Instance).Count());

        Assert.Equal("2", Assert.IsType<RunResult.Success>(KatLangEngine.Run(RowProgram(200))).ToDisplayString());
    }

    /// <summary>
    /// The shared empty lists are <see cref="Array.Empty{T}"/>: zero-length arrays, which no consumer can change. They
    /// report read-only, refuse every list mutation and have no element to overwrite, so sharing one instance across
    /// bodies cannot let one body's consumer alter another's lists.
    /// </summary>
    [Fact]
    public void SharedEmptyLists_AreZeroLengthArrays_ThatRefuseEveryMutation()
    {
        var root = SourceProvenance.ParseValid("A = 1\nA").Root;
        var body = Assert.IsType<Algorithm.User>(root.Properties.Single().Value);
        var item = root.Properties.Single();

        AssertImmutable(body.Properties, item);
        AssertImmutable(body.Opens, body.Output[0]);

        static void AssertImmutable<T>(IReadOnlyList<T> shared, T item)
        {
            var array = Assert.IsType<T[]>(shared);
            Assert.Same(Array.Empty<T>(), array);
            Assert.Empty(array);
            var list = (IList<T>)array;
            Assert.True(list.IsReadOnly);
            Assert.Throws<NotSupportedException>(() => list.Add(item));
            Assert.Throws<NotSupportedException>(() => list.Insert(0, item));
            Assert.Throws<NotSupportedException>(list.Clear);
            Assert.Throws<IndexOutOfRangeException>(() => array[0] = item);
            Assert.Empty(Array.Empty<T>());
        }
    }

    /// <summary>
    /// Record equality of elaborated bodies is unchanged by the shared empty lists. Two row-less bodies (<c>X = {}</c>,
    /// <c>Y = {}</c>) share the empty output bundle, so only their own lists tell them apart: they keep them, and stay
    /// unequal. Bodies with rows each have an output bundle of their own, which compares by reference.
    /// </summary>
    [Fact]
    public void BodiesWithoutRows_KeepTheirOwnLists_SoRecordEqualityIsUnchanged()
    {
        var root = SourceProvenance.ParseValid("X = {}\nY = {}\nA = 1\nB = 1\nA").Root;
        Algorithm.User Body(string name) => Assert.IsType<Algorithm.User>(root.Properties.Single(p => p.Name == name).Value);
        var (x, y, a, b) = (Body("X"), Body("Y"), Body("A"), Body("B"));

        Assert.Same(x.Output, y.Output);
        Assert.NotSame(x.Properties, y.Properties);
        Assert.NotSame(x.Opens, y.Opens);
        Assert.NotEqual(x, y);
        Assert.Same(a.Properties, b.Properties);
        Assert.NotEqual(a, b);
    }

    [Fact]
    public void IntermediateTrees_ShareEmptyPropertiesForRows_AndKeepDistinctAliasScopes()
    {
        const string program = """
            A = 1
            B = 1
            E = {}
            F = {}
            AliasA = A
            AliasB = A
            Capture(meta op) = op
            Inc(v) = v + 1
            R = Capture(Inc(0))
            LinkA = R.Algorithm
            LinkB = R.Algorithm
            A
            """;
        var detected = ParameterDetector.Detect(SourceProvenance.ParseSyntaxValidRoot(program));
        var resolved = ImplicitArgumentResolver.Resolve(detected);
        Assert.Empty(detected.Diagnostics);

        foreach (var root in new[] { detected.Root, resolved })
        {
            var (a, b) = (Body(root, "A"), Body(root, "B"));
            Assert.Same(Array.Empty<Property>(), a.Properties);
            Assert.Same(a.Properties, b.Properties);
            Assert.NotSame(a.Output, b.Output);
            Assert.NotEqual(a, b);

            var (e, f) = (Body(root, "E"), Body(root, "F"));
            Assert.Same(e.Output, f.Output);
            Assert.NotSame(e.Properties, f.Properties);
            Assert.NotEqual(e, f);
        }

        foreach (var (first, second, runtime) in new[] { ("AliasA", "AliasB", false), ("LinkA", "LinkB", true) })
        {
            var a = Assert.IsType<Algorithm.Alias>(Body(resolved, first));
            var b = Assert.IsType<Algorithm.Alias>(Body(resolved, second));
            Assert.Equal(runtime, a.HasRuntimeTarget);
            Assert.Equal(runtime, b.HasRuntimeTarget);
            Assert.NotSame(a.Properties, b.Properties);
            Assert.NotEqual(a, b);
        }

        static Algorithm Body(Algorithm root, string name) => root.Properties.Single(p => p.Name == name).Value;
    }

    /// <summary>
    /// An input-graph node creates its child and parent lists with its first edge: a leaf holds no child list and a row
    /// root no parent list (a constant row's one node holds neither), instead of two empty lists per node while its
    /// body is resolved (8 MiB live on a 2-MiB constant-row source). The edges read back unchanged.
    /// </summary>
    [Fact]
    public void InputGraph_LeavesAndRowRootsHoldNoEdgeList()
    {
        var root = SourceProvenance.ParseValid("F(x, y) = x + y\nC = 7\nG = F(1, 2) * C\nG").Root;
        Algorithm.User Body(string name) => Assert.IsType<Algorithm.User>(root.Properties.Single(p => p.Name == name).Value);

        var constant = new StaticInputGraph(AstHelpers.WrittenRows(Body("C")));
        Assert.Single(constant.Nodes);
        Assert.Equal(0, ObjectCensus.Of(constant).CountWhere(type => type == typeof(List<StaticInputGraph.Link>)));

        var formula = new StaticInputGraph(AstHelpers.WrittenRows(Body("G")));
        var nodes = formula.Nodes.Values.ToArray();
        var withChildren = nodes.Count(node => node.Children.Length > 0);
        var withParents = nodes.Count(node => node.Parents.Length > 0);
        Assert.True(withChildren < nodes.Length && withParents < nodes.Length);
        Assert.Equal(withChildren + withParents, ObjectCensus.Of(formula).CountWhere(type => type == typeof(List<StaticInputGraph.Link>)));

        // Every edge is read back from both ends: G's row `F(1, 2) * C` has the multiplication as its only root.
        var rowRoot = Assert.Single(nodes, node => node.Parents.Length == 0);
        Assert.Equal(1, rowRoot.Roots);
        Assert.Equal(nodes.Sum(node => node.Parents.Length), nodes.Sum(node => node.Children.Length));
        foreach (var node in nodes)
            foreach (var child in node.Children)
                Assert.Contains(formula.Nodes[child.Node].Parents.ToArray(), parent => ReferenceEquals(parent.Node, node.Expression));
        Assert.Equal(nodes.Length, formula.Topological.Count);
    }

    /// <summary>
    /// A level's input entries are built by name only. The per-index table both callers discarded was one array per
    /// level and pass — a fresh empty one for every leaf body, and two LOH arrays at the root of a ceiling-size
    /// source. An empty level then allocated its by-name table and nothing else; since 2026-11-18 it allocates
    /// nothing: every empty level, in both passes, gets the one shared, immutable empty map (both callers only count
    /// it and copy it into a signature map), while a level with properties still gets a by-name dictionary of its
    /// own. Bytes are averaged over many calls, so a background collection's quantum cannot decide them.
    /// </summary>
    [Fact]
    public void LeafLevelEntries_AllocateNoTable()
    {
        const int calls = 10_000;
        var method = typeof(ImplicitArgumentResolver).GetMethod("BuildPropertyEntries", BindingFlags.NonPublic | BindingFlags.Static)!;
        var parameters = method.GetParameters();
        var runType = parameters[3].ParameterType;
        var operation = StaticStructureAdmission.Create(SourceProvenance.ParseValid("A = 1\nA").Root).Operation;
        var run = Activator.CreateInstance(runType, BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic, null, [operation, null], null)!;
        var properties = System.Linq.Expressions.Expression.Parameter(typeof(IReadOnlyList<Property>));
        var runParameter = System.Linq.Expressions.Expression.Parameter(typeof(object));
        var build = System.Linq.Expressions.Expression.Lambda<Func<IReadOnlyList<Property>, object, object>>(
            System.Linq.Expressions.Expression.Call(method, properties,
                System.Linq.Expressions.Expression.Constant(DeclaringOwners.Root),
                System.Linq.Expressions.Expression.Constant(null, parameters[2].ParameterType),
                System.Linq.Expressions.Expression.Convert(runParameter, runType)),
            properties, runParameter).Compile();
        IReadOnlyList<Property> none = Array.Empty<Property>();

        var entries = Assert.IsType<System.Collections.ObjectModel.ReadOnlyDictionary<string, ImplicitArgumentResolver.VisibleProperty>>(build(none, run));
        Assert.Empty(entries);
        Assert.Same(entries, build(new List<Property>(), run));
        var level = PerCall(() => GC.KeepAlive(build(none, run)));
        Assert.True(level < 4, $"an empty level allocated {level:F1} B per call");

        // A level with properties keeps a by-name dictionary of its own.
        var declared = SourceProvenance.ParseValid("A = 1\nA").Root.Properties;
        var own = Assert.IsType<Dictionary<string, ImplicitArgumentResolver.VisibleProperty>>(build(declared, run));
        Assert.Equal(new[] { "A" }, own.Keys.ToArray());
        Assert.NotSame(own, build(declared, run));

        static double PerCall(Action action)
        {
            action();
            var before = GC.GetAllocatedBytesForCurrentThread();
            for (var i = 0; i < calls; i++)
                action();
            return (GC.GetAllocatedBytesForCurrentThread() - before) / (double)calls;
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
        private readonly HashSet<object> _objects = new(ReferenceEqualityComparer.Instance);

        public int CountWhere(Func<Type, bool> predicate) => _counts.Where(pair => predicate(pair.Key)).Sum(pair => pair.Value);

        /// <summary>The reachable heap objects that satisfy <paramref name="predicate"/>, each counted once.</summary>
        public int CountObjects(Func<object, bool> predicate) => _objects.Count(predicate);

        public static ObjectCensus Of(object root)
        {
            var census = new ObjectCensus();
            var seen = census._objects;
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
