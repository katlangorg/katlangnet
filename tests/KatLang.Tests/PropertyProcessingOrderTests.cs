namespace KatLang.Tests;

/// <summary>
/// The implicit-argument resolver's PROCESSING ORDER of one level's properties. The unified
/// formula-lifting law reads the processed signatures of opened, dotted and builtin-slot callees, so
/// every read must see the signature it would see in dependency order, whatever the declaration
/// order: HARD edges (the reads the sibling-order channel classifies) order the level; SOFT
/// preferences (the reads it can only anticipate) are honored among the properties the hard edges
/// leave ready; a read that still reaches a pending property processes it ON DEMAND, its pending
/// hard-dependency closure first — never ahead of a dependency still in progress, never for a member
/// of a sibling cycle (closed by hard or soft edges) or a property depending on one, and only as far
/// as the run's depth budget admits. Pinned here on synthetic order graphs; the source programs that
/// motivate each rule are pinned by <see cref="UnifiedFormulaLiftingTests"/>.
/// </summary>
public sealed class PropertyProcessingOrderTests
{
    /// <summary>A level of <paramref name="count"/> properties with the given hard and soft edges (<c>From</c> reads <c>To</c>).</summary>
    private static PropertyDependencyGraph Graph(int count, (int From, int To)[] hard, (int From, int To)[]? soft = null)
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
                SoftSiblingDependencyIndices = softBy[index].Distinct().Order().ToArray(),
            })
            .ToArray();
        return new PropertyDependencyGraph(properties, names, nodes);
    }

    /// <summary>A property loop over <paramref name="graph"/> that records every processing, runs <paramref name="reads"/> while a property is processed, and admits a demand unless <paramref name="refuse"/> says otherwise.</summary>
    private sealed class Level
    {
        public Level(PropertyDependencyGraph graph, Action<Level, int>? reads = null, Func<int, bool>? refuse = null)
        {
            Loop = new ImplicitArgumentResolver.PropertyLoop(
                graph,
                index =>
                {
                    Processed.Add(index);
                    reads?.Invoke(this, index);
                },
                index =>
                {
                    Admitted.Add(index);
                    if (refuse?.Invoke(index) == true)
                        return false;
                    ActiveDemands++;
                    return true;
                },
                () => ActiveDemands--);
        }

        public ImplicitArgumentResolver.PropertyLoop Loop { get; }

        public List<int> Processed { get; } = [];

        public List<int> Admitted { get; } = [];

        public int ActiveDemands { get; private set; }

        public void RunInOrder(PropertyDependencyGraph graph)
        {
            foreach (var index in graph.TopologicalOrder)
                Loop.Ensure(index);
        }
    }

    [Fact]
    public void WithoutSoftEdges_TheOrderIsPlainKahnInDeclarationOrder()
    {
        Assert.Equal([0, 1, 2, 3], Graph(4, []).TopologicalOrder);
        Assert.Equal([1, 3, 0, 2], Graph(4, [(0, 1), (2, 3)]).TopologicalOrder);
    }

    [Fact]
    public void SoftPreferences_AreHonoredAmongReadyProperties_ButNeverOverrideAHardEdge()
    {
        // P0 may read P1 and P1 may read P2, through opens the channel cannot classify.
        Assert.Equal([2, 1, 0], Graph(3, [], soft: [(0, 1), (1, 2)]).TopologicalOrder);

        // P1 reads P0 (hard), while P0 would like P1 first: the hard edge decides.
        Assert.Equal([0, 1], Graph(2, [(1, 0)], soft: [(0, 1)]).TopologicalOrder);

        // A soft ring cannot be honored everywhere: it is broken in declaration order.
        Assert.Equal([0, 2, 1], Graph(3, [], soft: [(0, 1), (1, 2), (2, 0)]).TopologicalOrder);
    }

    [Fact]
    public void CyclicIndices_AreTheMembersOfEverySiblingCycle_AndWhatHardDependsOnThem()
    {
        // A hard cycle, a property depending on it, and an independent one.
        Assert.Equal([0, 1, 2], Graph(4, [(0, 1), (1, 0), (2, 0)]).CyclicIndices.Order());

        // A cycle through soft preferences only; a hard dependent joins it, a soft one does not.
        Assert.Equal([0, 1, 2], Graph(4, [(2, 1)], soft: [(0, 1), (1, 0), (3, 0)]).CyclicIndices.Order());

        // A cycle closed by one soft and one hard edge.
        Assert.Equal([0, 1], Graph(3, [(1, 0)], soft: [(0, 1)]).CyclicIndices.Order());

        // Acyclic, hard and soft together: no cycle.
        Assert.Empty(Graph(4, [(1, 0), (3, 2)], soft: [(0, 2), (1, 3)]).CyclicIndices);
    }

    [Fact]
    public void CyclicIndices_OfALongRing_AreComputedWithoutGrowingTheHostStack()
    {
        // A recursive strongly-connected-components walk would need one frame per ring member.
        const int Count = 100_000;
        var soft = Enumerable.Range(0, Count).Select(static index => (index, (index + 1) % Count)).ToArray();
        var graph = Graph(Count, [], soft);
        var cyclic = 0;
        var thread = new Thread(() => cyclic = graph.CyclicIndices.Count, maxStackSize: 1024 * 1024);
        thread.Start();
        thread.Join();
        Assert.Equal(Count, cyclic);
    }

    [Fact]
    public void ADemand_ProcessesThePendingHardDependencyClosure_DependenciesFirst()
    {
        // P3 reads P1 and P2; P2 reads P0. Nothing is processed yet when P3 is demanded.
        var graph = Graph(5, [(3, 1), (3, 2), (2, 0)]);
        var level = new Level(graph);

        level.Loop.EnsureOnDemand(3);

        Assert.Equal([1, 0, 2, 3], level.Processed);
        Assert.Equal([1, 0, 2, 3], level.Admitted);
        Assert.Equal(0, level.ActiveDemands);

        // The level's own turn processes only what is left.
        level.RunInOrder(graph);
        Assert.Equal([1, 0, 2, 3, 4], level.Processed);
    }

    [Fact]
    public void ADemand_NeverProcessesAPropertyAheadOfADependencyStillInProgress()
    {
        // P2 reads P1, which reads P0. While P0 is processed, something it reads reaches P2 (an edge
        // no channel records): processing P2 then would read P0 unprocessed, so nothing is processed —
        // P0, whose turn came first, reads P2 unprocessed instead.
        var graph = Graph(3, [(2, 1), (1, 0)]);
        var level = new Level(graph, reads: static (level, index) =>
        {
            if (index == 0)
            {
                level.Loop.EnsureOnDemand(2);
                level.Loop.EnsureOnDemand(2);
            }
        });

        level.RunInOrder(graph);

        Assert.Equal([0, 1, 2], level.Processed);
        Assert.Empty(level.Admitted);
    }

    [Fact]
    public void ADemandFromAnEarlierProperty_ProcessesItsDependenciesAheadOfTheirTurnToo()
    {
        // P1 reads P0 (hard); P3 is processed first and reads P1 (an edge no channel records) while
        // P0 is still pending: the demand processes P0 and then P1.
        var graph = Graph(4, [(1, 0)]);
        var level = new Level(graph, reads: static (level, index) =>
        {
            if (index == 3)
                level.Loop.EnsureOnDemand(1);
        });

        level.Loop.Ensure(3);
        level.RunInOrder(graph);

        Assert.Equal([3, 0, 1, 2], level.Processed);
        Assert.Equal([0, 1], level.Admitted);
    }

    [Fact]
    public void ARefusedDemand_IsAdmittedOnceTheDependencyInProgressHasCompleted()
    {
        // P1 reads P0 (hard). While P0 is processed, a read reaches P1: refused. Once P0 has
        // completed, P2's read of P1 processes it ahead of its turn.
        var graph = Graph(3, [(1, 0)]);
        var level = new Level(graph, reads: static (level, index) =>
        {
            if (index is 0 or 2)
                level.Loop.EnsureOnDemand(1);
        });

        level.Loop.Ensure(0);
        Assert.Equal([0], level.Processed);
        Assert.Empty(level.Admitted);

        level.Loop.Ensure(2);
        Assert.Equal([0, 2, 1], level.Processed);
        Assert.Equal([1], level.Admitted);
    }

    [Fact]
    public void ADemand_NeverProcessesACycleMember_OrAPropertyDependingOnOne_Early()
    {
        // P0 and P1 open each other (soft); P2 reads P1 (hard); P3 is independent.
        var graph = Graph(4, [(2, 1)], soft: [(0, 1), (1, 0)]);
        var level = new Level(graph);

        level.Loop.EnsureOnDemand(0);
        level.Loop.EnsureOnDemand(1);
        level.Loop.EnsureOnDemand(2);
        Assert.Empty(level.Processed);

        level.Loop.EnsureOnDemand(3);
        Assert.Equal([3], level.Processed);
    }

    // ── The depth budget of on-demand processing ───────────────────────────────────────────

    /// <summary>A property whose one row is nested in <paramref name="lists"/> list literals.</summary>
    private static Property Deep(string name, int lists)
    {
        Expr row = new Expr.Num(1);
        for (var i = 0; i < lists; i++)
            row = new Expr.ListLiteral([row]);
        return new Property(name, new Algorithm.User(null, [], [], [], [row]));
    }

    [Fact]
    public void AnAdmittedDemand_ChargesItsOwnFramesUntilItEnds()
    {
        var budget = new ImplicitArgumentResolver.DemandDepthBudget();

        Assert.True(budget.TryEnter(Deep("P", 0), diagnostics: null, importSite: null));
        Assert.Equal(ImplicitArgumentResolver.DemandDepthBudget.FrameWeight, budget.LiveDepth);
        Assert.True(budget.TryEnter(Deep("Q", 0), diagnostics: null, importSite: null));
        Assert.Equal(2 * ImplicitArgumentResolver.DemandDepthBudget.FrameWeight, budget.LiveDepth);

        budget.Exit();
        budget.Exit();
        Assert.Equal(0, budget.LiveDepth);
    }

    [Fact]
    public void NestedDemands_Accumulate_UntilTheStructuralGateRefusesOne()
    {
        var budget = new ImplicitArgumentResolver.DemandDepthBudget();
        var diagnostics = new DiagnosticBag();
        // Bounded, so a budget that failed to accumulate fails here rather than looping forever.
        var admitted = 0;
        while (admitted < 10 * EvaluationLimits.MaxSupportedAstDepth && budget.TryEnter(Deep($"P{admitted}", 0), diagnostics, importSite: null))
            admitted++;

        // Every active demand holds its frames' charge, so nesting stops well inside the gate —
        // however shallow the properties — and the refused demand charged nothing.
        Assert.InRange(
            admitted,
            EvaluationLimits.MaxSupportedAstDepth / ImplicitArgumentResolver.DemandDepthBudget.FrameWeight - 2,
            EvaluationLimits.MaxSupportedAstDepth / ImplicitArgumentResolver.DemandDepthBudget.FrameWeight - 1);
        Assert.Equal(admitted * ImplicitArgumentResolver.DemandDepthBudget.FrameWeight, budget.LiveDepth);
        var refusal = Assert.Single(diagnostics);
        Assert.Equal(DiagnosticCode.AstDepthLimitExceeded, refusal.Code);
        Assert.StartsWith($"'P{admitted}' is reached through a chain of definitions that is too deep to elaborate safely", refusal.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ADeepProperty_IsRefusedOnceTheLiveDepthLeavesNoRoomForIt_AndReportedOnce()
    {
        var budget = new ImplicitArgumentResolver.DemandDepthBudget();
        var diagnostics = new DiagnosticBag();
        var site = new SourceSpan(new SourcePosition(3, 1), new SourcePosition(3, 5));

        // Far deeper than the gate leaves after a demand's own frames: refused at once.
        var tooDeep = Deep("TooDeep", EvaluationLimits.MaxSupportedAstDepth - 5);
        Assert.False(budget.TryEnter(tooDeep, diagnostics, site));
        Assert.False(budget.TryEnter(tooDeep, diagnostics, site));
        var refusal = Assert.Single(diagnostics);
        Assert.Equal(site, refusal.Span);
        Assert.Equal(0, budget.LiveDepth);

        // Admitted at the top, refused once enough demands are active.
        var deep = Deep("Deep", EvaluationLimits.MaxSupportedAstDepth - 55);
        Assert.True(budget.TryEnter(deep, diagnostics, site));
        budget.Exit();
        for (var i = 0; i < 5; i++)
            Assert.True(budget.TryEnter(Deep($"Shallow{i}", 0), diagnostics, site));
        Assert.False(budget.TryEnter(deep, diagnostics, site));
        Assert.Equal(2, diagnostics.Count);
    }

    [Fact]
    public void ADemand_StopsWhereTheDepthBudgetRefuses()
    {
        // The budget refuses P1: its dependency P0 was already processed (a complete closure of its
        // own), P1 and P2 stay pending for their turn.
        var graph = Graph(3, [(2, 1), (1, 0)]);
        var level = new Level(graph, refuse: static index => index == 1);

        level.Loop.EnsureOnDemand(2);

        Assert.Equal([0], level.Processed);
        Assert.Equal([0, 1], level.Admitted);
        Assert.Equal(0, level.ActiveDemands);
    }
}
