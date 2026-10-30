using Xunit;

namespace KatLang.Tests;

/// <summary>
/// B3 stage 0: the static query engine (<c>docs/design/static-structure-resolver-2026-10.md</c> § 3). Its final values
/// are the least fixed point of ordinary monotone equations, with OD-D seeds from the confirmed reference graph.
/// It runs any chain without host recursion. A1's unresolved decisions remain Unknown. Mixed paths have a separate
/// whole-graph oracle and adversarial regressions in StaticQueryPathTests.
/// The models below abstract the review witnesses: the owner-decision brief's A.3.1
/// and A.3.2, the navigated-body program `strata0`, and the plain OD-D cycle. They do not run KatLang source, because
/// no front-end pass reads the engine yet (stage B3-0).
/// </summary>
public sealed class StaticQueryEngineTests
{
    private enum Tri : byte
    {
        Unknown,
        No,
        Yes,
    }

    // ── A three-valued (Kleene) circuit, and the least-fixed-point oracle ──

    private readonly record struct Gate(char Op, int A, int B, Tri Value);

    private sealed class Circuit(Gate[] gates) : IStaticQueryDefinition<int, Tri>
    {
        public int Runs { get; private set; }

        public StaticQueryStep<Tri> Compute(int key, StaticQueryReader<int, Tri> reader)
        {
            Runs++;
            var gate = gates[key];
            if (gate.Op == 'c')
                return StaticQueryStep.Complete(gate.Value);
            var a = reader.Read(gate.A);
            var b = gate.Op is '&' or '|' ? reader.Read(gate.B) : Tri.Unknown;
            return StaticQueryStep.Complete(Apply(gate.Op, a, b));
        }

        public Tri Initial(int key) => Tri.Unknown;

        public Tri PathCycleValue => Tri.No;

        public bool ValueEquals(Tri left, Tri right) => left == right;

        public bool IsRefinement(Tri before, Tri after) => before == Tri.Unknown || before == after;
    }

    private static Tri Apply(char op, Tri a, Tri b) => op switch
    {
        '=' => a,
        '!' => a switch { Tri.Yes => Tri.No, Tri.No => Tri.Yes, _ => Tri.Unknown },
        '&' => a == Tri.No || b == Tri.No ? Tri.No : a == Tri.Yes && b == Tri.Yes ? Tri.Yes : Tri.Unknown,
        '|' => a == Tri.Yes || b == Tri.Yes ? Tri.Yes : a == Tri.No && b == Tri.No ? Tri.No : Tri.Unknown,
        _ => throw new InvalidOperationException($"unknown gate {op}"),
    };

    // Global Kleene iteration from all-Unknown: the least fixed point in the information order.
    private static Tri[] LeastFixedPoint(Gate[] gates)
    {
        var values = new Tri[gates.Length];
        while (true)
        {
            var next = new Tri[gates.Length];
            var changed = false;
            for (var k = 0; k < gates.Length; k++)
            {
                var gate = gates[k];
                next[k] = gate.Op == 'c' ? gate.Value : Apply(gate.Op, values[gate.A], gate.Op is '&' or '|' ? values[gate.B] : Tri.Unknown);
                changed |= next[k] != values[k];
            }

            if (!changed)
                return values;
            values = next;
        }
    }

    private static Gate[] RandomCircuit(Random random, int size)
    {
        var gates = new Gate[size];
        for (var k = 0; k < size; k++)
        {
            gates[k] = random.Next(10) switch
            {
                0 => new Gate('c', 0, 0, Tri.Yes),
                1 => new Gate('c', 0, 0, Tri.No),
                2 or 3 => new Gate('!', random.Next(size), 0, Tri.Unknown),
                4 => new Gate('=', random.Next(size), 0, Tri.Unknown),
                5 or 6 => new Gate('&', random.Next(size), random.Next(size), Tri.Unknown),
                _ => new Gate('|', random.Next(size), random.Next(size), Tri.Unknown),
            };
        }

        return gates;
    }

    private static string Describe(Gate[] gates)
        => string.Join("; ", gates.Select((gate, k) => gate.Op == 'c' ? $"{k}={gate.Value}" : $"{k}={gate.Op}({gate.A},{gate.B})"));

    [Fact]
    public void RandomCircuits_ReachTheLeastFixedPoint_InEveryDemandOrder()
    {
        // Round 43 of the first version of this sweep found a head that discarded only the results it owned.
        var random = new Random(20261027);
        for (var round = 0; round < 2000; round++)
        {
            var gates = RandomCircuit(random, random.Next(1, 40));
            var expected = LeastFixedPoint(gates);
            for (var order = 0; order < 4; order++)
            {
                var engine = new StaticQueryEngine<int, Tri>(new Circuit(gates));
                var keys = Enumerable.Range(0, gates.Length).OrderBy(_ => random.Next()).ToArray();
                foreach (var key in keys)
                {
                    var actual = engine.Get(key);
                    if (actual != expected[key])
                        Assert.Fail($"round {round}, order [{string.Join(", ", keys)}], key {key}: {actual}, expected {expected[key]}; {Describe(gates)}");
                }

                foreach (var key in keys)
                    Assert.True(engine.TryGetFinal(key, out var final) && final == expected[key]);
            }
        }
    }

    [Fact]
    public void ASharedDag_MakesEveryKeyFinalOnce()
    {
        // k = (k + 1) & (k + 2): each key refines once, notifying at most two readers.
        const int N = 2000;
        var gates = new Gate[N];
        for (var k = 0; k < N - 2; k++)
            gates[k] = new Gate('&', k + 1, k + 2, Tri.Unknown);
        gates[N - 2] = new Gate('c', 0, 0, Tri.Yes);
        gates[N - 1] = new Gate('c', 0, 0, Tri.Yes);
        var circuit = new Circuit(gates);
        var engine = new StaticQueryEngine<int, Tri>(circuit);

        Assert.Equal(Tri.Yes, engine.Get(0));
        Assert.Equal(N, engine.Statistics.Entries);
        Assert.True(circuit.Runs <= 3 * N, $"{circuit.Runs} runs for {N} keys");
        Assert.Equal(0, engine.Statistics.PathCycles);
    }

    [Fact]
    public void ADeepChainOfReads_RunsWithoutHostRecursion()
    {
        // 200,000 chained negations on a 256 KB thread: the engine's stack is on the heap.
        const int N = 200_000;
        var gates = new Gate[N];
        for (var k = 0; k < N - 1; k++)
            gates[k] = new Gate('!', k + 1, 0, Tri.Unknown);
        gates[N - 1] = new Gate('c', 0, 0, Tri.Yes);
        var circuit = new Circuit(gates);
        var engine = new StaticQueryEngine<int, Tri>(circuit);
        var actual = Tri.Unknown;
        Exception? failure = null;
        var thread = new Thread(
            () =>
            {
                try
                {
                    actual = engine.Get(0);
                }
                catch (Exception exception)
                {
                    failure = exception;
                }
            },
            maxStackSize: 256 * 1024);
        thread.Start();
        thread.Join();

        Assert.Null(failure);
        Assert.Equal((N - 1) % 2 == 0 ? Tri.Yes : Tri.No, actual);
        Assert.InRange(engine.Statistics.MaxPending, 1, N);
        Assert.True(circuit.Runs <= 2 * N, $"{circuit.Runs} runs for {N} keys");
    }

    // ── Hand-built models: string keys, one rule per key ──

    private sealed class Model(Dictionary<string, Func<StaticQueryReader<string, Tri>, StaticQueryStep<Tri>>> rules)
        : IStaticQueryDefinition<string, Tri>
    {
        public StaticQueryStep<Tri> Compute(string key, StaticQueryReader<string, Tri> reader) => rules[key](reader);

        public Tri Initial(string key) => Tri.Unknown;

        public Tri PathCycleValue => Tri.No;

        public bool ValueEquals(Tri left, Tri right) => left == right;

        public bool IsRefinement(Tri before, Tri after) => before == Tri.Unknown || before == after;
    }

    private static Func<StaticQueryReader<string, Tri>, StaticQueryStep<Tri>> Constant(Tri value)
        => _ => StaticQueryStep.Complete(value);

    // An input decision through a dot edge `R.n`: n is a fallback input exactly when R's chase is refused (R is then no
    // alias and has no member n); Unknown while R's verdict is.
    private static Func<StaticQueryReader<string, Tri>, StaticQueryStep<Tri>> FallbackIfRefused(string walk)
        => reader => StaticQueryStep.Complete(reader.Read(walk) switch { Tri.No => Tri.Yes, Tri.Yes => Tri.No, _ => Tri.Unknown });

    // A chase whose next hop is a body's row naming `name`: when name is the body's input the chase ends at a parameter
    // (a runtime reference: the walk is no cycle, Yes); otherwise it continues at `next` as a path step. Unknown input:
    // branch agreement.
    private static Func<StaticQueryReader<string, Tri>, StaticQueryStep<Tri>> ThroughRow(string input, string next)
        => reader =>
        {
            var isInput = reader.Read(input);
            if (isInput == Tri.Yes)
                return StaticQueryStep.Complete(Tri.Yes);
            if (isInput == Tri.No)
                return reader.Follow(next);
            // The head may be a runtime input: no definite path edge. Read the alternative ordinarily for agreement.
            return StaticQueryStep.Complete(reader.Read(next) == Tri.Yes ? Tri.Yes : Tri.Unknown);
        };

    // A chase step to the next body: refused (No) when it returns to a body it passed, otherwise the next body's verdict.
    private static Func<StaticQueryReader<string, Tri>, StaticQueryStep<Tri>> Follow(string next)
        => reader => reader.Follow(next);

    private static IEnumerable<string[]> Permutations(string[] items)
    {
        if (items.Length <= 1)
        {
            yield return items;
            yield break;
        }

        for (var i = 0; i < items.Length; i++)
        {
            var rest = items.Where((_, j) => j != i).ToArray();
            foreach (var tail in Permutations(rest))
                yield return [items[i], .. tail];
        }
    }

    private static void AssertInEveryOrder(
        Dictionary<string, Func<StaticQueryReader<string, Tri>, StaticQueryStep<Tri>>> rules, Dictionary<string, Tri> expected)
    {
        foreach (var order in Permutations([.. expected.Keys]))
        {
            var engine = new StaticQueryEngine<string, Tri>(new Model(rules));
            foreach (var key in order)
            {
                var actual = engine.Get(key);
                if (actual != expected[key])
                    Assert.Fail($"order [{string.Join(", ", order)}]: {key} is {actual}, expected {expected[key]}");
            }
        }
    }

    [Fact]
    public void A1_TwoConsistentAnswers_AreUndecided_InEveryOrder()
    {
        // Owner-decision brief A.3.1: x is an input exactly when R2 is no alias, R2 is one exactly when y is an input (its
        // row's y otherwise reads L3.y = P.R2, back to R2), and symmetrically. {x} and {y} are both consistent: A1 rejects.
        var rules = new Dictionary<string, Func<StaticQueryReader<string, Tri>, StaticQueryStep<Tri>>>
        {
            ["input:x"] = FallbackIfRefused("walk:R2"),
            ["input:y"] = FallbackIfRefused("walk:R"),
            ["walk:R"] = ThroughRow("input:x", "walk:R"),
            ["walk:R2"] = ThroughRow("input:y", "walk:R2"),
        };
        AssertInEveryOrder(rules, new() { ["input:x"] = Tri.Unknown, ["input:y"] = Tri.Unknown, ["walk:R"] = Tri.Unknown, ["walk:R2"] = Tri.Unknown });
    }

    [Fact]
    public void A1_NoConsistentAnswer_IsUndecided_InEveryOrder()
    {
        // A.3.2: n is an input exactly when R is no alias, R is one exactly when m is an input, and m is an input exactly
        // when n is (N.S.m with S = n): m iff not m.
        var rules = new Dictionary<string, Func<StaticQueryReader<string, Tri>, StaticQueryStep<Tri>>>
        {
            ["input:n"] = FallbackIfRefused("walk:R"),
            ["walk:R"] = ThroughRow("input:m", "walk:R"),
            ["input:m"] = reader => StaticQueryStep.Complete(reader.Read("input:n")),
        };
        AssertInEveryOrder(rules, new() { ["input:n"] = Tri.Unknown, ["walk:R"] = Tri.Unknown, ["input:m"] = Tri.Unknown });
    }

    [Fact]
    public void A1_ASelfReadThatDecidesNothing_IsDecided_InEveryOrder()
    {
        // Minimal rejection: a decision that reads itself but whose answer does not depend on it stays decided, and so does
        // everything that reads it.
        var rules = new Dictionary<string, Func<StaticQueryReader<string, Tri>, StaticQueryStep<Tri>>>
        {
            ["input:a"] = reader =>
            {
                var self = reader.Read("input:a");
                var b = reader.Read("input:b");
                return StaticQueryStep.Complete(Apply('|', self, b));
            },
            ["input:b"] = Constant(Tri.Yes),
            ["input:c"] = reader => StaticQueryStep.Complete(Apply('!', reader.Read("input:a"), Tri.Unknown)),
        };
        AssertInEveryOrder(rules, new() { ["input:a"] = Tri.Yes, ["input:b"] = Tri.Yes, ["input:c"] = Tri.No });
    }

    [Fact]
    public void OdD_AChaseThatReturnsToABodyItPassed_IsRefused_InEveryOrder()
    {
        // A = B, B = { … A }: neither is an alias, nor is C = A (its chase returns to A); D's chase ends: an alias.
        var rules = new Dictionary<string, Func<StaticQueryReader<string, Tri>, StaticQueryStep<Tri>>>
        {
            ["walk:A"] = Follow("walk:B"),
            ["walk:B"] = Follow("walk:A"),
            ["walk:C"] = Follow("walk:A"),
            ["walk:D"] = Follow("walk:E"),
            ["walk:E"] = Constant(Tri.Yes),
            ["walk:S"] = Follow("walk:S"),
        };
        AssertInEveryOrder(rules, new()
        {
            ["walk:A"] = Tri.No, ["walk:B"] = Tri.No, ["walk:C"] = Tri.No, ["walk:D"] = Tri.Yes, ["walk:E"] = Tri.Yes, ["walk:S"] = Tri.No,
        });
    }

    [Fact]
    public void NavigatedBody_TheChaseReadsTheBodysOwnInput_InEveryOrder()
    {
        // strata0 (probe-cases-r9h.txt). G.R's chase is a cycle, so `open G.R` provides no X and X is F's input. Ref's
        // chase (Ref → P → F) stops at F's parameter, so Ref is an alias of P, whichever query is demanded first. The two
        // front-end passes disagreed here because each derived F's input separately.
        var rules = new Dictionary<string, Func<StaticQueryReader<string, Tri>, StaticQueryStep<Tri>>>
        {
            ["walk:GR"] = Follow("walk:GR2"),
            ["walk:GR2"] = Follow("walk:GR"),
            ["input:FX"] = reader => StaticQueryStep.Complete(reader.Read("walk:GR") switch { Tri.Yes => Tri.No, Tri.No => Tri.Yes, _ => Tri.Unknown }),
            ["walk:F"] = ThroughRow("input:FX", "walk:CX"),
            ["walk:CX"] = Follow("walk:Ref"),
            ["walk:P"] = Follow("walk:F"),
            ["walk:Ref"] = Follow("walk:P"),
        };
        AssertInEveryOrder(rules, new()
        {
            ["walk:GR"] = Tri.No, ["walk:GR2"] = Tri.No, ["input:FX"] = Tri.Yes, ["walk:F"] = Tri.Yes,
            ["walk:CX"] = Tri.Yes, ["walk:P"] = Tri.Yes, ["walk:Ref"] = Tri.Yes,
        });
    }

    // ── Bounds and misuse ──

    private sealed class NestedHeads(int size, Tri seed) : IStaticQueryDefinition<int, Tri>
    {
        public Tri Initial(int key) => Tri.Unknown;

        public Tri PathCycleValue => Tri.No;

        public bool ValueEquals(Tri left, Tri right) => left == right;

        public bool IsRefinement(Tri before, Tri after) => before == Tri.Unknown || before == after;

        public StaticQueryStep<Tri> Compute(int key, StaticQueryReader<int, Tri> reader)
        {
            var previous = reader.Read(Math.Max(0, key - 1));
            var next = reader.Read(Math.Min(size - 1, key + 1));
            return StaticQueryStep.Complete(Apply('|', previous, key == size - 1 ? seed : next));
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void NestedMonotoneCycles_PropagateWithoutRestarting(bool seeded)
    {
        // One SCC, each key reading its two neighbours. The original engine needs 3*2^N-4 runs, even when
        // every answer stays Unknown. IR-04's worklist has no nested head convergence or provisional restarts.
        // Both the Unknown and seeded cases must now stay linear, not the previous seeded quadratic bound.
        foreach (var size in new[] { 8, 16, 32, 64, 256, 1024 })
        {
            var seed = seeded ? Tri.Yes : Tri.Unknown;
            var bound = seeded ? 3 * size : size;
            var engine = new StaticQueryEngine<int, Tri>(new NestedHeads(size, seed), limits: new(bound, 64));
            Assert.Equal(seed, engine.Get(0));
            for (var key = 0; key < size; key++)
                Assert.True(engine.TryGetFinal(key, out var value) && value == seed);
            Assert.InRange(engine.Statistics.Evaluations, 1, bound);
        }
    }

    [Fact]
    public void Cancellation_DuringARead_FaultsTheEngine_WithTheOriginalToken()
    {
        using var cancellation = new CancellationTokenSource();
        var rules = new Dictionary<string, Func<StaticQueryReader<string, Tri>, StaticQueryStep<Tri>>>
        {
            ["cancel"] = reader =>
            {
                cancellation.Cancel();
                reader.Read("other");
                return StaticQueryStep.Complete(Tri.Yes);
            },
            ["other"] = Constant(Tri.Yes),
        };
        var engine = new StaticQueryEngine<string, Tri>(new Model(rules), cancellationToken: cancellation.Token);
        var error = Assert.Throws<OperationCanceledException>(() => engine.Get("cancel"));
        Assert.Equal(cancellation.Token, error.CancellationToken);
        Assert.Equal(1, engine.Statistics.Evaluations);
        Assert.Throws<InvalidOperationException>(() => engine.TryGetFinal("other", out _));
    }

    [Fact]
    public void Cancellation_OnTheLastComputation_DoesNotPublishItsResult()
    {
        using var cancellation = new CancellationTokenSource();
        var rules = new Dictionary<string, Func<StaticQueryReader<string, Tri>, StaticQueryStep<Tri>>>
        {
            ["cancel"] = _ =>
            {
                cancellation.Cancel();
                return StaticQueryStep.Complete(Tri.Yes);
            },
        };
        var engine = new StaticQueryEngine<string, Tri>(new Model(rules), cancellationToken: cancellation.Token);
        Assert.Throws<OperationCanceledException>(() => engine.Get("cancel"));
        Assert.Throws<InvalidOperationException>(() => engine.Get("cancel"));
    }

    [Fact]
    public void Cancellation_BeforeDemand_ExecutesNoQuery()
    {
        using var cancellation = new CancellationTokenSource();
        cancellation.Cancel();
        var circuit = new Circuit([new Gate('c', 0, 0, Tri.Yes)]);
        var engine = new StaticQueryEngine<int, Tri>(circuit, cancellationToken: cancellation.Token);
        Assert.Throws<OperationCanceledException>(() => engine.Get(0));
        Assert.Equal(0, circuit.Runs);
    }

    [Fact]
    public void AnEvaluationBound_FaultsTheEngine()
    {
        var gates = Enumerable.Range(0, 100).Select(k => k < 99 ? new Gate('=', k + 1, 0, Tri.Unknown) : new Gate('c', 0, 0, Tri.Yes)).ToArray();
        var engine = new StaticQueryEngine<int, Tri>(new Circuit(gates), limits: new StaticQueryLimits(50, 64));

        Assert.Throws<StaticQueryLimitExceededException>(() => engine.Get(0));
        Assert.Throws<InvalidOperationException>(() => engine.Get(99));
    }

    [Fact]
    public void ADefinitionThatIsNotMonotone_IsRejectedAsANonRefinement()
    {
        // Unknown → Yes → No: reject the first incompatible observation rather than exhausting a head loop.
        var rules = new Dictionary<string, Func<StaticQueryReader<string, Tri>, StaticQueryStep<Tri>>>
        {
            ["flip"] = reader => StaticQueryStep.Complete(reader.Read("flip") == Tri.Yes ? Tri.No : Tri.Yes),
        };
        var engine = new StaticQueryEngine<string, Tri>(new Model(rules), limits: new StaticQueryLimits(long.MaxValue, 8));

        Assert.Contains("refinement", Assert.Throws<InvalidOperationException>(() => engine.Get("flip")).Message);
    }

    [Fact]
    public void ReadingOutsideTheReader_IsRefused()
    {
        StaticQueryEngine<string, Tri>? engine = null;
        var rules = new Dictionary<string, Func<StaticQueryReader<string, Tri>, StaticQueryStep<Tri>>>
        {
            ["outer"] = _ => StaticQueryStep.Complete(engine!.Get("inner")),
            ["inner"] = Constant(Tri.Yes),
        };
        engine = new StaticQueryEngine<string, Tri>(new Model(rules));

        Assert.Throws<InvalidOperationException>(() => engine.Get("outer"));
    }

    [Fact]
    public void DeclaringAPathAndReturningAnUnrelatedValue_IsRefused()
    {
        var rules = new Dictionary<string, Func<StaticQueryReader<string, Tri>, StaticQueryStep<Tri>>>
        {
            ["careless"] = reader =>
            {
                reader.Follow("other");
                return StaticQueryStep.Complete(Tri.Yes);
            },
            ["other"] = Constant(Tri.No),
        };
        var engine = new StaticQueryEngine<string, Tri>(new Model(rules));

        Assert.Throws<InvalidOperationException>(() => engine.Get("careless"));
    }
}
