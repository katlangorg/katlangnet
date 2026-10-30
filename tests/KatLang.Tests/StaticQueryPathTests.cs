namespace KatLang.Tests;

public sealed class StaticQueryPathTests
{
    private sealed class Rules(Dictionary<int, Func<StaticQueryReader<int, int>, StaticQueryStep<int>>> rules)
        : IStaticQueryDefinition<int, int>
    {
        public int Initial(int key) => 0;
        public int PathCycleValue => -1;
        public bool ValueEquals(int left, int right) => left == right;
        public bool IsRefinement(int before, int after) => before == 0 || before == after;
        public StaticQueryStep<int> Compute(int key, StaticQueryReader<int, int> reader) => rules[key](reader);
    }

    private static IEnumerable<int[]> Orders(int size)
    {
        if (size == 0) { yield return []; yield break; }
        foreach (var prefix in Orders(size - 1))
            for (var i = 0; i < size; i++)
                yield return [.. prefix.Take(i), size - 1, .. prefix.Skip(i)];
    }

    private static void Check(StaticQueryTestGate[] gates, int[] expected, IEnumerable<int[]> orders)
    {
        foreach (var order in orders)
        foreach (var reversed in new[] { false, true })
        {
            var engine = new StaticQueryEngine<int, int>(new StaticQueryTestModel(gates, reversed), limits: new(100_000, 8, 1000, 500_000));
            foreach (var key in order)
                Assert.True(engine.Get(key) == expected[key], $"key {key}; order [{string.Join(',', order)}]; reversed={reversed}");
            for (var key = 0; key < gates.Length; key++)
                Assert.True(engine.TryGetFinal(key, out var final) && final == expected[key]);
        }
    }

    [Fact]
    public void OriginalThreeKeyWitness_IsRefused_InEveryDemandAndReadOrder()
        => Check([new('f', 2, Ignored: 1), new('f', 2), new('f', 0)], [-1, -1, -1], Orders(3));

    [Fact]
    public void FailedParentContextRepairWitness_ReachesItsFunctionalPathVerdicts()
    {
        int[] next = [9, 0, 3, 8, 0, 0, 4, 8, 7, 6];
        int[] ignored = [1, 2, 6, 1, 0, 6, 6, 9, 9, 7];
        var gates = next.Select((target, key) => key == 8 ? new StaticQueryTestGate('c', Value: 1)
            : new StaticQueryTestGate('f', target, Ignored: ignored[key])).ToArray();
        Check(gates, [-1, -1, 1, 1, -1, -1, -1, 1, 1, -1],
            [[9, 2, 8, 5, 3, 0, 4, 7, 6, 1], [1, 6, 7, 4, 0, 3, 5, 8, 2, 9], Enumerable.Range(0, 10).ToArray()]);
    }

    [Fact]
    public void ExhaustiveThreeKeyFunctionalPaths_IgnoreOrdinaryDependencyCycles()
    {
        var orders = Orders(3).ToArray();
        for (var paths = 0; paths < 27; paths++)
        for (var dependencies = 0; dependencies < 27; dependencies++)
        for (var terminals = 0; terminals < 8; terminals++)
        {
            var gates = new StaticQueryTestGate[3];
            for (int key = 0, p = paths, d = dependencies; key < 3; key++, p /= 3, d /= 3)
                gates[key] = (terminals & (1 << key)) != 0 ? new('c', Value: 1) : new('f', p % 3, Ignored: d % 3);
            var expected = new int[3];
            for (var key = 0; key < 3; key++)
            {
                var at = key;
                var seen = new HashSet<int>();
                while (gates[at].Op == 'f' && seen.Add(at)) at = gates[at].A;
                expected[key] = gates[at].Op == 'c' ? 1 : -1;
            }
            Check(gates, expected, orders);
        }
    }

    [Fact]
    public void AnOrdinaryOrMixedDependencyCycle_IsUnknown_AndDoesNotSeedAPathRefusal()
    {
        foreach (var order in Orders(2))
        {
            var engine = new StaticQueryEngine<int, int>(new StaticQueryTestModel([new('=', 1), new('f', 0)]));
            foreach (var key in order) Assert.Equal(0, engine.Get(key));
            Assert.Equal(0, engine.Statistics.PathCycles);
        }
    }

    [Fact]
    public void KnownValueFlowsThroughADependencyScc_WithoutAPathCycle()
        => Check([new('|', 1, 2), new('f', 0), new('c', Value: 1)], [1, 1, 1], Orders(3));

    [Fact]
    public void ADependencyCanObserveAPathRefusal_WithoutBecomingAReferenceReturn()
        => Check([new('f', 1), new('f', 0), new('!', 0)], [-1, -1, 1], Orders(3));

    [Fact]
    public void UnknownAlternative_UsesBranchAgreement_AndNeverCommitsAReference()
    {
        // The static route may return, but the head may instead be an input. A1 keeps it unresolved.
        Check([new('t', 1, 0), new('!', 0)], [0, 0], Orders(2));
        // Both possible routes are acyclic: the unknown guard decides nothing.
        Check([new('t', 1, 2), new('=', 1), new('c', Value: 1)], [1, 0, 1], Orders(3));
    }

    [Fact]
    public void ANewTailIntoAFinalCyclicComponent_DoesNotRecomputeTheComponent()
    {
        const int size = 10_000;
        var gates = Enumerable.Range(0, size).Select(key => new StaticQueryTestGate('f', key == 0 ? 0 : key - 1)).ToArray();
        var model = new StaticQueryTestModel(gates);
        var engine = new StaticQueryEngine<int, int>(model, limits: new(3 * size, 2, size, 2 * size));
        for (var key = 0; key < size; key++) Assert.Equal(-1, engine.Get(key));
        Assert.Equal(size, model.Runs);
        Assert.Equal(1, engine.Statistics.PathCycles);
        Assert.Equal(size, engine.Statistics.Entries);
    }

    [Fact]
    public void DeepReferencePaths_UseNoHostRecursion_AndKeepAllEndpointIdentities()
    {
        const int size = 200_000;
        var gates = Enumerable.Range(0, size).Select(key => key == size - 1
            ? new StaticQueryTestGate('c', Value: 19) : new StaticQueryTestGate('f', key + 1)).ToArray();
        var engine = new StaticQueryEngine<int, int>(new StaticQueryTestModel(gates), limits: new(2 * size, 2, size, size));
        Exception? failure = null;
        var result = 0;
        var thread = new Thread(() => { try { result = engine.Get(0); } catch (Exception error) { failure = error; } }, 256 * 1024);
        thread.Start();
        thread.Join();
        Assert.Null(failure);
        Assert.Equal(19, result);
        Assert.Equal(size, engine.Statistics.Computations);
        Assert.Equal(size - 1, engine.Statistics.PathEdges);
        Assert.Equal(0, engine.Statistics.PathCycles);
        // Component representatives are private graph bookkeeping, not the returned algorithm identity.
        var identities = new StaticQueryEngine<int, int>(new StaticQueryTestModel([new('f', 2), new('f', 3), new('c', Value: 19), new('c', Value: 23)]));
        Assert.Equal(19, identities.Get(0));
        Assert.Equal(23, identities.Get(1));
    }

    [Fact]
    public void ALongCycle_IsDetectedOnce_WithinLinearWork()
    {
        const int size = 50_000;
        var gates = Enumerable.Range(0, size).Select(key => new StaticQueryTestGate('f', (key + 1) % size)).ToArray();
        var engine = new StaticQueryEngine<int, int>(new StaticQueryTestModel(gates), limits: new(3 * size, 2, size, size));
        Assert.Equal(-1, engine.Get(0));
        Assert.Equal(1, engine.Statistics.PathCycles);
        Assert.InRange(engine.Statistics.Evaluations, size, 3 * size);
    }

    [Fact]
    public void FinalAnswersArePublishedOnlyAtQuiescence_AndCachedAcrossRootOrders()
    {
        var model = new StaticQueryTestModel([new('!', 1), new('=', 2), new('c', Value: 1)]);
        var engine = new StaticQueryEngine<int, int>(model);
        Assert.False(engine.TryGetFinal(0, out _));
        Assert.Equal(-1, engine.Get(0));
        var runs = model.Runs;
        Assert.Equal(1, engine.Get(1));
        Assert.Equal(1, engine.Get(2));
        Assert.Equal(runs, model.Runs);
    }

    [Fact]
    public void DynamicOrdinarySubscriptions_AreRemovedWhenABranchStopsReadingThem()
    {
        var engine = new StaticQueryEngine<int, int>(new Rules(new()
        {
            [0] = r =>
            {
                if (r.Read(1) != 0) return StaticQueryStep.Complete(1);
                r.Read(2); // An unresolved alternative is observed, not speculatively selected.
                return StaticQueryStep.Complete(0);
            },
            [1] = _ => StaticQueryStep.Complete(1),
            [2] = _ => StaticQueryStep.Complete(-1),
        }));
        Assert.Equal(1, engine.Get(0));
        Assert.Equal(1, engine.Statistics.Dependencies); // Only the control is still read, not its old alternative.
    }

    [Fact]
    public void APathDeclaredBeforeItsGuardIsDecided_IsRejectedIfItRewires()
    {
        var engine = new StaticQueryEngine<int, int>(new Rules(new()
        {
            [0] = r => r.Follow(r.Read(1) == 0 ? 2 : 3),
            [1] = _ => StaticQueryStep.Complete(1),
            [2] = _ => StaticQueryStep.Complete(1),
            [3] = _ => StaticQueryStep.Complete(1),
        }));
        Assert.Contains("rewired", Assert.Throws<InvalidOperationException>(() => engine.Get(0)).Message);
    }

    [Fact]
    public void MultiplePathDeclarationsAndMissingEquations_AreRejected()
    {
        var multiple = new StaticQueryEngine<int, int>(new Rules(new()
        {
            [0] = r => { r.Follow(1); return r.Follow(2); },
            [1] = _ => StaticQueryStep.Complete(1), [2] = _ => StaticQueryStep.Complete(1),
        }));
        Assert.Throws<InvalidOperationException>(() => multiple.Get(0));
        var missing = new StaticQueryEngine<int, int>(new Rules(new() { [0] = _ => default }));
        Assert.Throws<InvalidOperationException>(() => missing.Get(0));
    }

    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    public void EntryAndReadLimits_StopFanoutBeforeUnboundedAllocation(int kind)
    {
        var engine = new StaticQueryEngine<int, int>(new Rules(new()
        {
            [0] = r => { for (var key = 1; ; key++) r.Read(key); },
        }), limits: kind == 0 ? new(100, 2, 5, 100) : new(100, 2, 100, 4));
        Assert.Throws<StaticQueryLimitExceededException>(() => engine.Get(0));
        Assert.Equal(5, engine.Statistics.Entries);
        Assert.Throws<InvalidOperationException>(() => engine.Get(0));
    }

    private sealed class Ascending : IStaticQueryDefinition<int, int>
    {
        public int Initial(int key) => 0;
        public int PathCycleValue => 0;
        public bool ValueEquals(int left, int right) => left == right;
        public bool IsRefinement(int before, int after) => after >= before;
        public StaticQueryStep<int> Compute(int key, StaticQueryReader<int, int> reader) => StaticQueryStep.Complete(reader.Read(key) + 1);
    }

    [Fact]
    public void AnUnboundedMonotoneDomain_StopsAtItsPerKeyRefinementLimit()
    {
        var engine = new StaticQueryEngine<int, int>(new Ascending(), limits: new(100, 8));
        Assert.Throws<StaticQueryLimitExceededException>(() => engine.Get(0));
        Assert.Equal(8, engine.Statistics.ValueChanges);
    }

    private sealed class WideInputs(int width, bool cascade) : IStaticQueryDefinition<int, int>
    {
        public int Initial(int key) => 0;
        public int PathCycleValue => -1;
        public bool ValueEquals(int left, int right) => left == right;
        public bool IsRefinement(int before, int after) => before == 0 || before == after;
        public StaticQueryStep<int> Compute(int key, StaticQueryReader<int, int> reader)
        {
            if (key != 0)
                return StaticQueryStep.Complete(cascade && key < width ? reader.Read(key + 1) : 1);
            var ready = true;
            for (var input = 1; input <= width; input++)
                ready &= reader.Read(input) == 1;
            return StaticQueryStep.Complete(ready ? 1 : 0);
        }
    }

    [Theory]
    [InlineData(1000)]
    [InlineData(4000)]
    public void WideIndependentInputs_AreBatchedBeforeTheirReaderRunsAgain(int width)
    {
        var engine = new StaticQueryEngine<int, int>(new WideInputs(width, false),
            limits: new(3L * width, 2, width + 1, 3L * width));
        Assert.Equal(1, engine.Get(0));
        Assert.Equal(2L * width, engine.Statistics.Reads);
        Assert.Equal(width + 2L, engine.Statistics.Computations);
    }

    [Fact]
    public void CascadingWideInputs_RespectTheReadBoundEvenWhenOpaqueCallbacksRescan()
    {
        // The engine bounds callback reads as well as worklist events. A wide callback over a refining
        // chain can still perform quadratic reads; production definitions need bounded fan-in or aggregation.
        var engine = new StaticQueryEngine<int, int>(new WideInputs(256, true),
            limits: new(10_000, 2, 257, 2048));
        Assert.Contains("read bound", Assert.Throws<StaticQueryLimitExceededException>(() => engine.Get(0)).Message);
        Assert.Equal(2048, engine.Statistics.Reads);
        Assert.Throws<InvalidOperationException>(() => engine.TryGetFinal(0, out _));
    }

    // Independent Jacobi rounds and fresh path tracing. This shares no incremental graph/scheduling code with the engine.
    private static int[] WholeGraphOracle(StaticQueryTestGate[] gates)
    {
        var values = new int[gates.Length];
        for (var round = 0; round <= gates.Length + 1; round++)
        {
            var following = Enumerable.Repeat(-1, gates.Length).ToArray();
            var next = new int[gates.Length];
            for (var key = 0; key < gates.Length; key++)
            {
                var g = gates[key];
                var a = values[g.A];
                var b = values[g.B];
                if (g.Op == 'f' || g.Op == 't' && a == -1)
                {
                    following[key] = g.Op == 'f' ? g.A : g.B;
                    continue;
                }
                next[key] = g.Op switch
                {
                    'c' => g.Value,
                    '=' => a,
                    '!' => -a,
                    '&' => a == -1 || b == -1 ? -1 : a == 1 && b == 1 ? 1 : 0,
                    '|' => a == 1 || b == 1 ? 1 : a == -1 && b == -1 ? -1 : 0,
                    't' => a == 1 || b == 1 ? 1 : 0,
                    _ => throw new InvalidOperationException(),
                };
            }
            for (var key = 0; key < gates.Length; key++)
            {
                if (following[key] < 0) continue;
                var seen = new HashSet<int>();
                var at = key;
                while (following[at] >= 0 && seen.Add(at)) at = following[at];
                next[key] = following[at] >= 0 ? -1 : values[following[key]];
            }
            for (var key = 0; key < gates.Length; key++)
                Assert.True(values[key] == 0 || values[key] == next[key], "Oracle model lost information");
            if (values.SequenceEqual(next)) return values;
            values = next;
        }
        throw new InvalidOperationException("Whole-graph oracle did not converge");
    }

    [Fact]
    public void RandomGuardedPathsAndOrdinaryCircuits_AgreeWithTheWholeGraphOracle()
    {
        var random = new Random(20261028);
        char[] operators = ['c', '=', '!', '&', '|', 'f', 'f', 't', 't'];
        for (var round = 0; round < 2000; round++)
        {
            var size = random.Next(1, 32);
            var gates = Enumerable.Range(0, size).Select(_ => new StaticQueryTestGate(
                operators[random.Next(operators.Length)], random.Next(size), random.Next(size), random.Next(-1, 2),
                random.Next(2) == 0 ? -1 : random.Next(size))).ToArray();
            var expected = WholeGraphOracle(gates);
            var orders = Enumerable.Range(0, 4).Select(_ => Enumerable.Range(0, size).OrderBy(_ => random.Next()).ToArray()).ToArray();
            Check(gates, expected, orders);
        }
    }

    private sealed class ObservedCycle(int size, CancellationTokenSource cancellation) : IStaticQueryDefinition<int, int>
    {
        private int _refusals;
        public int Initial(int key) => 0;
        public int PathCycleValue => -1;
        public bool ValueEquals(int left, int right)
        {
            if (left != right && right == -1 && ++_refusals == 8) cancellation.Cancel();
            return left == right;
        }
        public bool IsRefinement(int before, int after) => before == 0 || before == after;
        public StaticQueryStep<int> Compute(int key, StaticQueryReader<int, int> reader) => reader.Follow((key + 1) % size);
    }

    [Fact]
    public void CancellationDuringPathComponentPropagation_RemainsTerminal_WithItsOriginalToken()
    {
        using var cancellation = new CancellationTokenSource();
        var engine = new StaticQueryEngine<int, int>(new ObservedCycle(1000, cancellation), cancellationToken: cancellation.Token);
        var error = Assert.Throws<OperationCanceledException>(() => engine.Get(0));
        Assert.Equal(cancellation.Token, error.CancellationToken);
        Assert.Equal(7, engine.Statistics.ValueChanges);
        Assert.Throws<InvalidOperationException>(() => engine.TryGetFinal(0, out _));
    }

    private sealed class SpelledPaths : IStaticQueryDefinition<string, int>
    {
        public int Initial(string key) => 0;
        public int PathCycleValue => -1;
        public bool ValueEquals(int left, int right) => left == right;
        public bool IsRefinement(int before, int after) => before == 0 || before == after;
        public StaticQueryStep<int> Compute(string key, StaticQueryReader<string, int> reader)
            => reader.Follow(string.Equals(key, "A", StringComparison.OrdinalIgnoreCase) ? "b" : "a");
    }

    [Fact]
    public void GraphAndCacheIdentity_UseTheSuppliedKeyComparer()
    {
        var engine = new StaticQueryEngine<string, int>(new SpelledPaths(), StringComparer.OrdinalIgnoreCase);
        Assert.Equal(-1, engine.Get("A"));
        Assert.Equal(-1, engine.Get("B"));
        Assert.Equal(2, engine.Statistics.Entries);
        Assert.Equal(1, engine.Statistics.PathCycles);
    }

    [Fact]
    public void ADefinitionCannotAbsorbAReaderLimitAndPublishAnAnswer()
    {
        StaticQueryLimitExceededException? observed = null;
        var engine = new StaticQueryEngine<int, int>(new Rules(new()
        {
            [0] = r =>
            {
                try { r.Read(1); r.Read(2); }
                catch (StaticQueryLimitExceededException error) { observed = error; }
                return StaticQueryStep.Complete(1);
            },
            [1] = _ => StaticQueryStep.Complete(0),
        }), limits: new(100, 2, 10, 1));
        var terminal = Assert.Throws<StaticQueryLimitExceededException>(() => engine.Get(0));
        Assert.Same(observed, terminal);
        Assert.Throws<InvalidOperationException>(() => engine.TryGetFinal(0, out _));
    }

    private sealed class InfinitePath : IStaticQueryDefinition<int, int>
    {
        public int Initial(int key) => 0;
        public int PathCycleValue => -1;
        public bool ValueEquals(int left, int right) => left == right;
        public bool IsRefinement(int before, int after) => before == 0 || before == after;
        public StaticQueryStep<int> Compute(int key, StaticQueryReader<int, int> reader) => reader.Follow(key + 1);
    }

    [Fact]
    public void AnUnboundedReferenceGraph_StopsBeforeExceedingTheEntryLimit()
    {
        var engine = new StaticQueryEngine<int, int>(new InfinitePath(), limits: new(1024, 2, 128, 1024));
        Assert.Throws<StaticQueryLimitExceededException>(() => engine.Get(0));
        Assert.Equal(128, engine.Statistics.Entries);
        Assert.Throws<InvalidOperationException>(() => engine.Get(0));
    }
}
