namespace KatLang.Tests;

/// <summary>
/// A SIBLING CYCLE'S DECLARATION-ORDER FALLBACK IS CONFINED TO THE CYCLE (X-04, October 2026).
///
/// <para>The implicit-argument resolver processes a level's properties in dependency order, so every
/// formula reads the PROCESSED signature of what it uses; a hard sibling cycle falls back to
/// declaration order among its members (a member processed first reads the others unprocessed).
/// When soft preferences close a larger cycle, its internal hard-scheduler order is retained too,
/// while consumers outside the combined component follow every member. The order used to append, on
/// the first stall, EVERY property still waiting, cycle members and the acyclic properties waiting
/// on them alike, in declaration order, so a consumer declared before the cycle read an intermediate
/// signature: <c>C = B + z</c> / <c>A = { Helper = B + 0 ⏎ x + 1 }</c> / <c>B = y + A</c> /
/// <c>C(1, 2, 3)</c> inferred <c>C(z, y)</c> and failed with an arity mismatch, while the same
/// program with <c>C</c> declared last inferred <c>C(z, y, x)</c> and gave 7. The order is now Kahn's
/// over the CONDENSATION (<see cref="PropertyDependencyGraph.TopologicalOrder"/>): a cycle is one
/// unit, released only when no property outside a cycle is ready, its members in declaration order,
/// and a property depending on it follows all of its members.</para>
///
/// <para>Pinned here three ways: the order's laws on synthetic graphs against an INDEPENDENT oracle
/// (brute-force reachability components, and the former algorithm for levels without a cycle, which
/// must order exactly as before); a declaration-order METAMORPHIC matrix over source programs of every
/// graph shape — every permutation must agree on the consumer's inferred signature, its value, the
/// diagnostics and the host-call log, on all six execution routes; and the editor's view of the
/// consumer. <see cref="PropertyProcessingOrderTests"/> pins the soft preferences, the cyclic set and
/// on-demand processing.</para>
/// </summary>
public sealed class SiblingDependencyCycleTests
{
    // ── Synthetic order graphs ───────────────────────────────────────────────────────────

    /// <summary>A level of <paramref name="count"/> properties with the given hard and soft edges (<c>From</c> reads <c>To</c>).</summary>
    private static PropertyDependencyGraph Graph(int count, IEnumerable<(int From, int To)> hard, IEnumerable<(int From, int To)>? soft = null)
    {
        var properties = Enumerable.Range(0, count)
            .Select(static index => new Property($"P{index}", new Algorithm.User(null, [], [], [], [new Expr.Num(index)])))
            .ToArray();
        var names = properties.Select(static (property, index) => (property.Name, index)).ToDictionary(static pair => pair.Name, static pair => pair.index, StringComparer.Ordinal);
        var hardBy = hard.ToLookup(static edge => edge.From, static edge => edge.To);
        var softBy = (soft ?? []).ToLookup(static edge => edge.From, static edge => edge.To);
        var nodes = Enumerable.Range(0, count)
            .Select(index => new PropertyDependencyNode(index, hardBy[index].Distinct().Order().ToArray())
            {
                SoftSiblingDependencyIndices = softBy[index].Distinct().Except(hardBy[index]).Order().ToArray(),
            })
            .ToArray();
        return new PropertyDependencyGraph(properties, names, nodes);
    }

    /// <summary>
    /// The independent component oracle: two properties share a component exactly when each reaches
    /// the other through hard edges (brute-force reachability, no Tarjan). Returns, per property, the
    /// smallest index of its component.
    /// </summary>
    private static int[] OracleComponentKeys(PropertyDependencyGraph graph, bool includeSoft = false)
    {
        var count = graph.Count;
        var reaches = new bool[count, count];
        for (var start = 0; start < count; start++)
        {
            var pending = new Stack<int>([start]);
            reaches[start, start] = true;
            while (pending.TryPop(out var property))
            {
                foreach (var dependency in graph[property].SiblingDependencyIndices.Concat(includeSoft ? graph[property].SoftSiblingDependencyIndices : []))
                {
                    if (!reaches[start, dependency])
                    {
                        reaches[start, dependency] = true;
                        pending.Push(dependency);
                    }
                }
            }
        }

        var keys = new int[count];
        for (var property = 0; property < count; property++)
        {
            keys[property] = property;
            for (var other = 0; other < property; other++)
            {
                if (reaches[property, other] && reaches[other, property])
                {
                    keys[property] = other;
                    break;
                }
            }
        }

        return keys;
    }

    /// <summary>
    /// The order's laws, checked against the oracle: a permutation; every hard read ACROSS components
    /// processed first (a property depending on a cycle follows ALL of its members); every cycle
    /// contiguous with its members in declaration order (its processing-order fallback); and, for a
    /// level without soft preferences, every property that reaches no cycle ahead of every cycle (a
    /// cycle is released only when no property outside one is ready).
    /// </summary>
    private static void AssertCondensationOrder(PropertyDependencyGraph graph)
    {
        var order = graph.TopologicalOrder;
        var count = graph.Count;
        Assert.Equal(Enumerable.Range(0, count), order.Order());

        var position = new int[count];
        for (var index = 0; index < count; index++)
            position[order[index]] = index;

        var keys = OracleComponentKeys(graph);
        var combinedKeys = OracleComponentKeys(graph, includeSoft: true);
        for (var property = 0; property < count; property++)
        {
            foreach (var dependency in graph[property].SiblingDependencyIndices)
            {
                if (keys[dependency] != keys[property])
                    Assert.True(position[dependency] < position[property], $"P{property} reads P{dependency} outside its unit but is ordered first: [{string.Join(", ", order)}]");
            }
        }

        // Preferences can close a cycle too. Its old internal order remains, but every read
        // outside the combined component must follow ALL of that provider's members.
        for (var property = 0; property < count; property++)
        {
            foreach (var dependency in graph[property].SiblingDependencyIndices.Concat(graph[property].SoftSiblingDependencyIndices))
            {
                if (combinedKeys[dependency] == combinedKeys[property])
                    continue;
                foreach (var member in Enumerable.Range(0, count).Where(i => combinedKeys[i] == combinedKeys[dependency]))
                    Assert.True(position[member] < position[property], $"P{property} precedes unsettled provider P{member}: [{string.Join(", ", order)}]");
            }
        }

        foreach (var cycle in Enumerable.Range(0, count).GroupBy(property => keys[property]).Where(static unit => unit.Count() > 1))
        {
            var members = cycle.Order().ToArray();
            var first = position[members[0]];
            Assert.Equal(members, order.Skip(first).Take(members.Length));
        }

        if (Enumerable.Range(0, count).Any(property => graph[property].SoftSiblingDependencyIndices.Count > 0))
            return;

        var inCycle = Enumerable.Range(0, count).Select(property => keys.Count(key => key == keys[property]) > 1).ToArray();
        var reachesCycle = new bool[count];
        foreach (var property in order)
        {
            reachesCycle[property] = inCycle[property]
                || graph[property].SiblingDependencyIndices.Any(dependency => reachesCycle[dependency]);
        }

        var firstCycleMember = Enumerable.Range(0, count).Where(property => inCycle[property]).Select(property => position[property]).DefaultIfEmpty(count).Min();
        foreach (var property in Enumerable.Range(0, count).Where(property => !reachesCycle[property]))
            Assert.True(position[property] < firstCycleMember, $"P{property} depends on no cycle but follows one: [{string.Join(", ", order)}]");
    }

    /// <summary>
    /// The order BEFORE X-04 — plain Kahn with soft preferences, every property still waiting appended in
    /// declaration order — kept as the oracle for levels without a cycle, which must order exactly as
    /// they always have.
    /// </summary>
    private static List<int> FormerOrder(PropertyDependencyGraph graph)
    {
        var count = graph.Count;
        var inDegree = new int[count];
        var dependents = Enumerable.Range(0, count).Select(static _ => new List<int>()).ToArray();
        var softDependents = Enumerable.Range(0, count).Select(static _ => new List<int>()).ToArray();
        var softPending = new int[count];
        for (var property = 0; property < count; property++)
        {
            foreach (var dependency in graph[property].SiblingDependencyIndices)
            {
                dependents[dependency].Add(property);
                inDegree[property]++;
            }

            foreach (var soft in graph[property].SoftSiblingDependencyIndices)
            {
                softDependents[soft].Add(property);
                softPending[property]++;
            }
        }

        var queue = new Queue<int>();
        var blocked = new SortedSet<(long Sequence, int Index)>();
        var sequence = new long[count];
        var next = 0L;
        void MakeReady(int property)
        {
            if (softPending[property] == 0)
            {
                queue.Enqueue(property);
                return;
            }

            sequence[property] = next++;
            blocked.Add((sequence[property], property));
        }

        for (var property = 0; property < count; property++)
        {
            if (inDegree[property] == 0)
                MakeReady(property);
        }

        var result = new List<int>();
        while (queue.Count > 0 || blocked.Count > 0)
        {
            int property;
            if (queue.Count > 0)
            {
                property = queue.Dequeue();
            }
            else
            {
                property = blocked.Min.Index;
                blocked.Remove(blocked.Min);
            }

            result.Add(property);
            foreach (var dependent in dependents[property])
            {
                if (--inDegree[dependent] == 0)
                    MakeReady(dependent);
            }

            foreach (var dependent in softDependents[property])
            {
                if (--softPending[dependent] == 0 && blocked.Remove((sequence[dependent], dependent)))
                    queue.Enqueue(dependent);
            }
        }

        result.AddRange(Enumerable.Range(0, count).Where(property => inDegree[property] > 0));
        return result;
    }

    /// <summary>Every ordering of <paramref name="items"/>.</summary>
    private static IEnumerable<T[]> Permutations<T>(IReadOnlyList<T> items)
    {
        if (items.Count <= 1)
        {
            yield return [.. items];
            yield break;
        }

        for (var index = 0; index < items.Count; index++)
        {
            var rest = items.Where((_, other) => other != index).ToArray();
            foreach (var tail in Permutations(rest))
                yield return [items[index], .. tail];
        }
    }

    /// <summary>
    /// A named-property graph laid out in one declaration order: the edges of <paramref name="reads"/>
    /// (a property reads the listed ones) over the indices <paramref name="declared"/> gives the names.
    /// </summary>
    private static PropertyDependencyGraph Declared(IReadOnlyList<string> declared, IReadOnlyDictionary<string, string[]> reads)
    {
        var index = declared.Select(static (name, position) => (name, position)).ToDictionary(static pair => pair.name, static pair => pair.position);
        return Graph(declared.Count, reads.SelectMany(read => read.Value.Select(target => (index[read.Key], index[target]))));
    }

    private static int[] Positions(PropertyDependencyGraph graph, IReadOnlyList<string> declared, params string[] names)
    {
        var order = graph.TopologicalOrder.ToList();
        return [.. names.Select(name => order.IndexOf(declared.ToList().IndexOf(name)))];
    }

    [Fact]
    public void ATwoPropertyCycle_IsOneUnit_InDeclarationOrder()
    {
        Assert.Equal([0, 1], Graph(2, [(0, 1), (1, 0)]).TopologicalOrder);
        Assert.Equal([0, 1, 2], Graph(3, [(0, 1), (1, 2), (2, 0)]).TopologicalOrder);
    }

    /// <summary>The canonical shape: <c>A ⇄ B → C</c>, in every declaration order.</summary>
    [Fact]
    public void ADependentOfACycle_FollowsAllOfItsMembers_InEveryDeclarationOrder()
    {
        var reads = new Dictionary<string, string[]> { ["A"] = ["B"], ["B"] = ["A"], ["C"] = ["B"] };
        foreach (var declared in Permutations(["C", "A", "B"]))
        {
            var graph = Declared(declared, reads);
            AssertCondensationOrder(graph);
            var positions = Positions(graph, declared, "A", "B", "C");
            Assert.True(positions[2] > positions[0] && positions[2] > positions[1], $"order {string.Join("", declared)}: C must follow A and B");
        }

        // The X-04 witness's declaration order: C, A, B. Formerly the stall appended all three in
        // declaration order ([C, A, B]); now the cycle goes first, then its consumer.
        var witness = Declared(["C", "A", "B"], reads);
        Assert.Equal([0, 1, 2], FormerOrder(witness));
        Assert.Equal([1, 2, 0], witness.TopologicalOrder);
    }

    [Fact]
    public void AnUpstreamProducer_PrecedesTheCycleThatReadsIt()
    {
        // P → A ⇄ B: P is processed before the cycle, whatever the declaration order.
        var reads = new Dictionary<string, string[]> { ["A"] = ["B", "P"], ["B"] = ["A"] };
        foreach (var declared in Permutations(["A", "B", "P"]))
        {
            var graph = Declared(declared, reads);
            AssertCondensationOrder(graph);
            var positions = Positions(graph, declared, "P", "A", "B");
            Assert.True(positions[0] < positions[1] && positions[0] < positions[2]);
        }
    }

    [Fact]
    public void AChainAndADiamondAfterACycle_FollowIt_InEveryDeclarationOrder()
    {
        var chain = new Dictionary<string, string[]> { ["A"] = ["B"], ["B"] = ["A"], ["C"] = ["B"], ["D"] = ["C"], ["E"] = ["D"] };
        foreach (var declared in Permutations(["A", "B", "C", "D", "E"]))
        {
            var graph = Declared(declared, chain);
            AssertCondensationOrder(graph);
            Assert.Equal(["C", "D", "E"], graph.TopologicalOrder.Skip(2).Select(index => declared[index]));
        }

        var diamond = new Dictionary<string, string[]> { ["A"] = ["B"], ["B"] = ["A"], ["C"] = ["B"], ["D"] = ["B"], ["E"] = ["C", "D"] };
        foreach (var declared in Permutations(["A", "B", "C", "D", "E"]))
        {
            var graph = Declared(declared, diamond);
            AssertCondensationOrder(graph);
            Assert.Equal("E", declared[graph.TopologicalOrder[^1]]);
        }
    }

    [Fact]
    public void AThreeMemberCycle_WithAcyclicDependents_IsOneUnit()
    {
        // A → B → C → A, with D reading C and E reading D and A.
        var reads = new Dictionary<string, string[]> { ["A"] = ["B"], ["B"] = ["C"], ["C"] = ["A"], ["D"] = ["C"], ["E"] = ["D", "A"] };
        foreach (var declared in Permutations(["A", "B", "C", "D", "E"]))
        {
            var graph = Declared(declared, reads);
            AssertCondensationOrder(graph);
            Assert.Equal(["D", "E"], graph.TopologicalOrder.Skip(3).Select(index => declared[index]));
        }
    }

    [Fact]
    public void TwoIndependentCycles_AndConsumersOfEitherOrBoth()
    {
        // A ⇄ B and P ⇄ Q; C reads B, R reads Q, X reads both cycles.
        var reads = new Dictionary<string, string[]>
        {
            ["A"] = ["B"], ["B"] = ["A"], ["P"] = ["Q"], ["Q"] = ["P"], ["C"] = ["B"], ["R"] = ["Q"], ["X"] = ["A", "P"],
        };
        string[] names = ["A", "B", "P", "Q", "C", "R", "X"];
        var random = new Random(4);
        for (var sample = 0; sample < 200; sample++)
        {
            var declared = names.OrderBy(_ => random.Next()).ToArray();
            var graph = Declared(declared, reads);
            AssertCondensationOrder(graph);
            var positions = Positions(graph, declared, "A", "B", "P", "Q", "C", "R", "X");
            Assert.True(positions[4] > Math.Max(positions[0], positions[1]));
            Assert.True(positions[5] > Math.Max(positions[2], positions[3]));
            Assert.True(positions[6] > positions[..4].Max());
        }
    }

    [Fact]
    public void ACycleDependingOnAnotherCycle_FollowsIt()
    {
        // A ⇄ B, and P ⇄ Q where P also reads B: the second cycle waits for the first.
        var reads = new Dictionary<string, string[]> { ["A"] = ["B"], ["B"] = ["A"], ["P"] = ["Q", "B"], ["Q"] = ["P"] };
        foreach (var declared in Permutations(["P", "Q", "A", "B"]))
        {
            var graph = Declared(declared, reads);
            AssertCondensationOrder(graph);
            Assert.Equal(["A", "B"], graph.TopologicalOrder.Take(2).Select(index => declared[index]).Order());
        }
    }

    [Fact]
    public void SoftPreferences_DecideAmongReadyCycles_AndPullACycleAheadOfASoftBlockedProperty()
    {
        // Two ready cycles, P0 ⇄ P1 and P2 ⇄ P3, where P0 may read P2 (an `open` the channel cannot
        // classify): the cycle it prefers goes first, although declared later.
        Assert.Equal([2, 3, 0, 1], Graph(4, [(0, 1), (1, 0), (2, 3), (3, 2)], soft: [(0, 2)]).TopologicalOrder);

        // P0 may read P1, a member of the ready cycle P1 ⇄ P2: the cycle goes before the property
        // that prefers it, which formerly read P1 unprocessed.
        Assert.Equal([1, 2, 0], Graph(3, [(1, 2), (2, 1)], soft: [(0, 1)]).TopologicalOrder);
        Assert.Equal([0, 1, 2], FormerOrder(Graph(3, [(1, 2), (2, 1)], soft: [(0, 1)])));
    }

    [Fact]
    public void LevelsWithoutACycle_OrderExactlyAsTheyAlwaysHave()
    {
        // Random hard-acyclic levels with soft preferences in both directions. With no combined
        // cycle the order equals the former one; otherwise only whole components move, preserving
        // their internal order while protecting their acyclic consumers.
        var random = new Random(17);
        for (var sample = 0; sample < 400; sample++)
        {
            var count = random.Next(1, 14);
            var rank = Enumerable.Range(0, count).OrderBy(_ => random.Next()).ToArray();
            var hard = new List<(int, int)>();
            var soft = new List<(int, int)>();
            for (var from = 0; from < count; from++)
            {
                for (var to = 0; to < count; to++)
                {
                    if (from == to)
                        continue;
                    var roll = random.Next(10);
                    if (roll < 2 && rank[from] > rank[to])
                        hard.Add((from, to));
                    else if (roll == 2)
                        soft.Add((from, to));
                }
            }

            var graph = Graph(count, hard, soft);
            var combinedKeys = OracleComponentKeys(graph, includeSoft: true);
            if (combinedKeys.Distinct().Count() == count)
                Assert.Equal(FormerOrder(graph), graph.TopologicalOrder);
            else
            {
                AssertCondensationOrder(graph);
                // The repair moves only whole components; their internal fallback is unchanged.
                var former = FormerOrder(graph);
                foreach (var unit in Enumerable.Range(0, count).GroupBy(i => combinedKeys[i]))
                    Assert.Equal(former.Where(unit.Contains), graph.TopologicalOrder.Where(unit.Contains));
            }
        }
    }

    [Fact]
    public void RandomLevels_SatisfyTheCondensationLaws()
    {
        var random = new Random(23);
        for (var sample = 0; sample < 600; sample++)
        {
            var count = random.Next(1, 12);
            var hard = new List<(int, int)>();
            var soft = new List<(int, int)>();
            var withSoft = sample % 3 == 0;
            for (var from = 0; from < count; from++)
            {
                for (var to = 0; to < count; to++)
                {
                    if (from == to)
                        continue;
                    var roll = random.Next(12);
                    if (roll < 2)
                        hard.Add((from, to));
                    else if (withSoft && roll == 2)
                        soft.Add((from, to));
                }
            }

            AssertCondensationOrder(Graph(count, hard, soft));
        }
    }

    [Fact]
    public void ALongCycleWithALongChainAfterIt_IsOrderedWithoutGrowingTheHostStack()
    {
        // A ring of 100 000 properties read by a chain of 100 000: one strongly connected component
        // and one long tail, ordered on a 1 MiB thread (a recursive walk would need a frame per link).
        const int Ring = 100_000;
        const int Chain = 100_000;
        var hard = new List<(int, int)>(Ring + Chain);
        for (var index = 0; index < Ring; index++)
            hard.Add((index, (index + 1) % Ring));
        for (var index = 0; index < Chain; index++)
            hard.Add((Ring + index, index == 0 ? Ring - 1 : Ring + index - 1));
        var graph = Graph(Ring + Chain, hard);

        IReadOnlyList<int>? order = null;
        var thread = new Thread(() => order = graph.TopologicalOrder, maxStackSize: 1024 * 1024);
        thread.Start();
        thread.Join();

        Assert.NotNull(order);
        Assert.Equal(Enumerable.Range(0, Ring + Chain), order);
    }

    // ── Source programs: declaration order is unobservable outside the cycle ───────────────

    /// <summary>
    /// One graph shape as a program: its declarations (each one or more lines), the property whose
    /// signature the shape decides, and the row that calls it. Every declaration order of the program
    /// must give <paramref name="Signature"/> and the observation of <paramref name="Value"/> (traced),
    /// identically on all six routes. None of these cycles depends on its members' relative order: a
    /// member processed first reads the others' INPUT signatures, which here already carry every
    /// parameter their own lifting keeps (contrast
    /// <see cref="TheCycleMayDependOnItsMembersOrder_ButNeverOnWhereItsConsumerIsDeclared"/>).
    /// </summary>
    public sealed record Shape(string Name, string[] Declarations, string Focus, string Call, string Signature, string Value)
    {
        public override string ToString() => Name;
    }

    private const string CycleA = "A = { H = B + 0\n  x + 1 }";
    private const string CycleB = "B = y + A";

    public static TheoryData<Shape> Shapes() =>
    [
        // The X-04 witness: C = B + z read B's intermediate C(z, y) when declared first.
        new Shape("canonical", ["C = B + z", CycleA, CycleB], "C", "C(1, 2, 3)", "C(z, y, x)", "7"),
        // A three-member cycle A → B → C → A with an acyclic dependent.
        new Shape(
            "three-member-cycle",
            ["D = C + d", "A = { H = B + 0\n  a + 1 }", "B = { H = C + 0\n  b + 2 }", "C = c + A"],
            "D", "D(1, 2, 3)", "D(d, c, a)", "7"),
        new Shape("chain-after-cycle", ["E = D + v", "D = C + w", "C = B + z", CycleA, CycleB], "E", "E(1, 2, 3, 4, 5)", "E(v, w, z, y, x)", "16"),
        new Shape("diamond-after-cycle", ["E = C + D", "C = B + p", "D = B + q", CycleA, CycleB], "E", "E(1, 2, 3, 4)", "E(p, y, x, q)", "17"),
        new Shape(
            "two-cycles-one-consumer",
            ["C = B + Q", CycleA, CycleB, "P = { H = Q + 0\n  u + 10 }", "Q = v + P"],
            "C", "C(1, 2, 3, 4)", "C(y, x, v, u)", "21"),
        // An acyclic producer the cycle reads (processed before it).
        new Shape("upstream-producer", ["C = B + z", CycleA, "B = y + A + P", "P = p * 10"], "C", "C(1, 2, 3, 4)", "C(z, y, x, p)", "47"),
        // A dotted read of a cycle member's public member (a hard edge to the head).
        new Shape(
            "dotted-member-read",
            ["C = A.V + z", "A = { public V = B + x\n  0 }", "B = { H = A.V + 0\n  y + 1 }"],
            "C", "C(1, 2, 3)", "C(z, x, y)", "7"),
        // A read through the consumer's own `open` of a cycle member (a soft preference).
        new Shape(
            "opened-member-read",
            ["D = { open A\n  V + z }", "A = { public V = B + x\n  0 }", "B = { H = A.V + 0\n  y + 1 }"],
            "D", "D(1, 2, 3)", "D(z, x, y)", "7"),
        // A closed consumer forwards its own bindings to the cycle member's FINAL signature (the parser
        // elaborates clause groups after plain properties, so it never preceded the cycle).
        new Shape("explicit-closed-consumer", ["C(z, y, x) = B + z", CycleA, CycleB], "C", "C(1, 2, 3)", "C(z, y, x)", "7"),
        // A property reading itself is no cycle (the channel records no self-edge) and absorbs nothing.
        new Shape("self-reading-property", ["C = S + z", "S = { H = S + 0\n  s + 5 }"], "C", "C(1, 2)", "C(z, s)", "8"),
    ];

    private static string Program(IEnumerable<string> declarations, string row)
        => string.Join("\n", declarations) + "\n" + row;

    [Theory]
    [MemberData(nameof(Shapes))]
    public async Task EveryDeclarationOrder_InfersTheSameSignature_AndEvaluatesTheSame_OnEveryRoute(Shape shape)
    {
        foreach (var declared in Permutations(shape.Declarations))
        {
            var source = Program(declared, $"trace({shape.Call})");
            var parsed = SourceProvenance.ParseValid(source);
            var focus = Assert.Single(parsed.Root.Properties, property => property.Name == shape.Focus);
            Assert.Equal(shape.Signature, CallableSignature.FromAlgorithm(focus.Name, focus.Value).DisplayText);

            var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
            Assert.True(observation is { Kind: "ok" } && observation.Value == shape.Value,
                $"{shape.Name} in the order\n{source}\ngave {observation}");
            Assert.Equal([$"trace({shape.Value})"], observation.HostCalls);
        }
    }

    /// <summary>
    /// A cycle whose result DOES depend on its members' relative order: <c>A</c>'s parameter <c>p</c>
    /// comes from lifting the producer <c>P</c>, so it is not in <c>A</c>'s input signature, and a
    /// <c>B</c> processed before <c>A</c> reads <c>A</c> without it — the cycle's processing-order
    /// fallback, which the language rules permit. What X-04 forbids is a consumer that depends on
    /// where IT is declared: for each relative order of <c>A</c> and <c>B</c>, every position of the
    /// consumer and the producer gives the same signature and the same outcome on every route.
    /// </summary>
    [Fact]
    public async Task TheCycleMayDependOnItsMembersOrder_ButNeverOnWhereItsConsumerIsDeclared()
    {
        string[] declarations = ["C = B + z", "A = { H = B + 0\n  P + 1 }", "B = y + A", "P = p * 10"];
        foreach (var declared in Permutations(declarations))
        {
            var aFirst = Array.FindIndex(declared, static d => d.StartsWith("A ", StringComparison.Ordinal))
                < Array.FindIndex(declared, static d => d.StartsWith("B ", StringComparison.Ordinal));
            var source = Program(declared, "trace(C(1, 2, 3))");
            var root = SourceProvenance.ParseValid(source).Root;
            var consumer = Assert.Single(root.Properties, static property => property.Name == "C");
            Assert.Equal(aFirst ? "C(z, y, p)" : "C(z, y)", CallableSignature.FromAlgorithm(consumer.Name, consumer.Value).DisplayText);

            var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
            if (aFirst)
            {
                Assert.True(observation is { Kind: "ok", Value: "34" }, $"{source}\ngave {observation}");
                Assert.Equal(["trace(34)"], observation.HostCalls);
            }
            else
            {
                Assert.Equal("err", observation.Kind);
                Assert.StartsWith("ArityMismatch: ", Assert.Single(observation.Errors), StringComparison.Ordinal);
                Assert.Contains("Callable `C(z, y)` expects 2 arguments, but was called with 3 arguments.", observation.Errors[0], StringComparison.Ordinal);
                Assert.Empty(observation.HostCalls);
            }
        }
    }

    /// <summary>
    /// X-04 × X-07: whether an output-less consumer of a cycle is a function — and so the front-end
    /// error an output-less function is — depends on the cycle member's SETTLED signature (<c>B</c>'s
    /// input signature has no parameter; lifting gives it <c>x</c>). Formerly the consumer declared
    /// first read the intermediate one and was a valid container (the program printed 5); declared
    /// last it reached the evaluator as an unpositioned failure. Every order is now the same
    /// positioned front-end error, and nothing runs.
    /// </summary>
    [Fact]
    public async Task AnOutputLessConsumerOfACycle_IsJudgedOnTheSettledSignature_InEveryDeclarationOrder()
    {
        foreach (var declared in Permutations(["F = { a, b = B + 0, 1 }", CycleA, "B = A + 0"]))
        {
            var source = Program(declared, "trace(5)");
            var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
            Assert.Equal("parse", observation.Kind);
            Assert.Empty(observation.HostCalls);
            var error = Assert.Single(observation.Errors);
            var line = Array.IndexOf(source.Split('\n'), "F = { a, b = B + 0, 1 }") + 1;
            Assert.StartsWith($"{nameof(KatLangErrorCode.ExplicitParametersRequireOutput)}: This algorithm takes the implicit parameter 'x' but does not define an output.", error, StringComparison.Ordinal);
            Assert.EndsWith($"@ [{line}:1, {line}:2)", error, StringComparison.Ordinal);
        }
    }

    /// <summary>
    /// The editor sees what evaluation sees: in every declaration order the consumer's reference
    /// resolves to the cycle member's declaration and the consumer's parameters are the settled ones.
    /// </summary>
    [Fact]
    public void TheEditorModel_OfAConsumerOfACycle_IsTheSameInEveryDeclarationOrder()
    {
        foreach (var declared in Permutations(["C = B + z", CycleA, CycleB]))
        {
            var source = Program(declared, "C(1, 2, 3)");
            var model = Semantics.SemanticModelBuilder.Build(SourceProvenance.ParseValid(source).Parsed);
            var lines = source.Split('\n');
            var consumerLine = Array.IndexOf(lines, "C = B + z") + 1;
            var declarationLine = Array.FindIndex(lines, static line => line.StartsWith("B = ", StringComparison.Ordinal)) + 1;

            var resolution = model.FindResolutionAt(new SourcePosition(consumerLine, 5));
            Assert.NotNull(resolution);
            Assert.Equal("B", resolution.ResolvedDeclaration?.Name);
            Assert.Equal(new SourceSpan(declarationLine, 1, declarationLine, 2), resolution.ResolvedDeclaration?.Span);

            var consumer = Assert.Single(model.FindProperties("C"));
            Assert.Equal(["z", "y", "x"], consumer.Parameters.Select(static parameter => parameter.DisplayName));
        }
    }

    /// <summary>
    /// Inside a genuine cycle the declaration-order fallback stands, as the language rules permit: the
    /// member processed first reads the other unprocessed. With <c>A</c> declared first, the helper
    /// inside <c>A</c> reads <c>B</c>'s INPUT signature and calls <c>B(y)</c>; with <c>B</c> first, it
    /// reads <c>B(y, x)</c> and forwards <c>A</c>'s own <c>x</c> — wherever the consumer is declared.
    /// </summary>
    [Fact]
    public void InsideTheCycle_TheDeclarationOrderFallbackStands()
    {
        static int HelperCallArguments(IReadOnlyList<string> declared)
        {
            var root = SourceProvenance.ParseValid(Program(declared, "C(1, 2, 3)")).Root;
            var a = Assert.IsType<Algorithm.User>(Assert.Single(root.Properties, property => property.Name == "A").Value);
            var helper = Assert.IsType<Algorithm.User>(Assert.Single(a.Properties, property => property.Name == "H").Value);
            var sum = Assert.IsType<Expr.Binary>(Assert.Single(helper.Output));
            return Assert.IsType<Expr.Call>(sum.Left).Args.Count;
        }

        Assert.Equal(1, HelperCallArguments(["C = B + z", CycleA, CycleB]));
        Assert.Equal(1, HelperCallArguments([CycleA, "C = B + z", CycleB]));
        Assert.Equal(1, HelperCallArguments([CycleA, CycleB, "C = B + z"]));
        Assert.Equal(2, HelperCallArguments(["C = B + z", CycleB, CycleA]));
        Assert.Equal(2, HelperCallArguments([CycleB, "C = B + z", CycleA]));
        Assert.Equal(2, HelperCallArguments([CycleB, CycleA, "C = B + z"]));
    }
}
