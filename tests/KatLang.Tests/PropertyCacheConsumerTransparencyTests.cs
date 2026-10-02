using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// ZERO-PARAMETER PROPERTY CACHING DOES NOT DEPEND ON THE CONSUMER (September 2026).
///
/// <para>A zero-parameter property is evaluated once per run for each resolved property
/// binding; repeated VALUE access to that same binding reuses the result; a shadowing
/// property is a different binding with its own entry; <c>A()</c> explicitly requests a
/// fresh evaluation and neither reads nor replaces the entry. Cache identity follows the
/// resolved binding, never the spelling, and HOW A PROPERTY VALUE IS CONSUMED DOES NOT
/// AFFECT CACHING: a builtin VALUE slot (written or dotted), the <c>.string</c> receiver,
/// a user call, a forwarded parameter, a callback body, a selection, a collection element,
/// and a planned loop all receive the value the property access produced.</para>
///
/// <para>Before this rule a builtin argument that NAMED a property received the property's
/// own algorithm as its value channel and re-ran the body on every demand
/// (<c>sum(A)</c>, <c>A.max</c>, <c>if(c, A, 0)</c>, <c>A.string</c>), so the value a
/// consumer saw depended on the consumer. The evidence here is deterministic host
/// instrumentation (an operation that counts its invocations inside the property body),
/// the run-scoped cache's own request/evaluation counts, and seeded random streams for
/// the end-to-end picture. Lean: <c>CoreTests/PropertyCacheConsumers.lean</c>.</para>
/// </summary>
public class PropertyCacheConsumerTransparencyTests
{
    /// <summary>
    /// Shared helpers. <c>A</c> is a list and <c>N</c> a number (the <c>.string</c>
    /// intrinsic converts a numeric receiver); every evaluation of either BODY invokes the
    /// host operation <c>Tick</c> exactly once, so the invocation count is the number of
    /// times the property's body ran.
    /// </summary>
    private const string Helpers = """
        A = [Tick(), 2]
        N = Tick() + 4
        Box = { public V = Tick() + 9 }
        Keep(s) = s
        Add(e, acc) = e + acc
        Double(x) = x * 2
        Big(x) = x > 1
        Stats(xs) = sum(xs), max(xs)
        Show(v) = v.string
        Once(w) = if(w > 0, w, 0)
        Twice(v) = Once(v) + sum(v)
        Apply(f, xs) = map(xs, f)
        Pass(v) = Apply(Double, v)
        """;

    /// <summary>
    /// One ordinary read of the named property plus one consumer of it. Every consumer
    /// must receive the read's cached value, so the property's body runs exactly once.
    /// </summary>
    public static TheoryData<string, string> Consumers() => new()
    {
        // Builtin collection slots, written and dotted.
        { "A", "sum(A)" }, { "A", "A.sum" }, { "A", "max(A)" }, { "A", "A.max" },
        { "A", "min(A)" }, { "A", "avg(A)" }, { "A", "count(A)" }, { "A", "A.count" },
        { "A", "first(A)" }, { "A", "last(A)" }, { "A", "A.last" },
        { "A", "take(A, 1)" }, { "A", "A.take(1)" }, { "A", "skip(A, 1)" },
        { "A", "order(A)" }, { "A", "orderDesc(A)" }, { "A", "distinct(A)" },
        { "A", "contains(A, 2)" }, { "A", "atoms(A)" }, { "A", "count((A*, A*))" },
        // The lazy `if`, both branches.
        { "A", "if(true, A, 0)" }, { "A", "if(false, 0, A)" },
        // Loop initial state and the reduce initial accumulator.
        { "A", "repeat(Keep, 2, A)" }, { "A", "reduce([], Add, A)" },
        // Higher-order builtins: the collection is the cached value.
        { "A", "map(A, Double)" }, { "A", "A.map(Double)" }, { "A", "filter(A, Big)" },
        { "A", "reduce(A, Add, 0)" }, { "A", "A.reduce(Add, 0)" }, { "A", "map(A, {x * 2})" },
        // User algorithms, direct, dotted, and forwarded into a higher-order builtin.
        { "A", "Stats(A)" }, { "A", "A.Stats" }, { "A", "Apply(Double, A)" }, { "A", "Pass(A)" },
        // Value positions.
        { "A", "A:0" }, { "A", "[A, A]" }, { "A", "(A, A)" }, { "A", "A == A" },
        // Numeric consumers, the `.string` intrinsic, loops, and forwarding.
        { "N", "N.string" }, { "N", "Show(N)" }, { "N", "N.Show" }, { "N", "if(N > 0, N, 0)" },
        { "N", "N + N" }, { "N", "Twice(N)" }, { "N", "sum(N)" }, { "N", "range(N, 7)" },
        { "N", "repeat(Keep, 1, N)" }, { "N", "while({s + 1, s < 7}, N)" }, { "N", "reduce([1], Add, N)" },
        // An inline callback reading the property on every element.
        { "N", "map([1, 2, 3], {x + N})" }, { "N", "[1, 2].filter({x < N}).count" },
        // A structurally navigated member.
        { "Box.V", "Box.V.string" }, { "Box.V", "sum(Box.V)" }, { "Box.V", "Box.V.sum" },
        { "Box.V", "if(true, Box.V, 0)" }, { "Box.V", "Show(Box.V)" }, { "Box.V", "Box.V + 1" },
    };

    private sealed class Counter
    {
        private int _count;

        public int Count => Volatile.Read(ref _count);

        public void Increment() => Interlocked.Increment(ref _count);
    }

    private static RunOptions SyncTick(Counter counter, int value = 1)
        => new()
        {
            HostOperations = HostOperations.Create(HostOperation.Create("Tick", (_, _) =>
            {
                counter.Increment();
                return new Result.Atom(value);
            })),
        };

    /// <summary>An ASYNCHRONOUS <c>Tick</c> that genuinely suspends, forcing the async twins.</summary>
    private static RunOptions AsyncTick(Counter counter)
        => new()
        {
            HostOperations = HostOperations.Create(HostOperation.CreateAsync("Tick", async (_, _) =>
            {
                counter.Increment();
                await Task.Yield();
                return new Result.Atom(1);
            })),
        };

    private static string DisplayOf(RunResult result)
        => Assert.IsType<RunResult.Success>(result).ToDisplayString();

    // ── 1. Consumer transparency: sync and async ─────────────────────────────

    [Theory]
    [MemberData(nameof(Consumers))]
    public void EveryConsumer_ReceivesTheCachedValue_ThePropertyBodyRunsOnce(string read, string consumer)
    {
        var readFirst = new Counter();
        var readFirstDisplay = DisplayOf(KatLangEngine.Run($"{Helpers}\n{read}\n{consumer}", SyncTick(readFirst)));
        Assert.Equal(1, readFirst.Count);

        // The consumer ORDER is irrelevant: a consumer that reads first stores the entry
        // the later ordinary read reuses.
        var consumerFirst = new Counter();
        var consumerFirstDisplay = DisplayOf(KatLangEngine.Run($"{Helpers}\n{consumer}\n{read}", SyncTick(consumerFirst)));
        Assert.Equal(1, consumerFirst.Count);

        // Two consumers after the read: still one evaluation.
        var twice = new Counter();
        DisplayOf(KatLangEngine.Run($"{Helpers}\n{read}\n{consumer}\n{consumer}", SyncTick(twice)));
        Assert.Equal(1, twice.Count);

        static string[] Rows(string display) => display.Split('\n').Select(static row => row.Trim()).ToArray();
        Assert.Equal(Rows(readFirstDisplay), Enumerable.Reverse(Rows(consumerFirstDisplay)));
    }

    [Theory]
    [MemberData(nameof(Consumers))]
    public async Task EveryConsumer_ReceivesTheCachedValue_OnTheAsyncTwinsToo(string read, string consumer)
    {
        var syncCounter = new Counter();
        var syncDisplay = DisplayOf(KatLangEngine.Run($"{Helpers}\n{read}\n{consumer}", SyncTick(syncCounter)));

        // An asynchronous host operation routes the whole run through the async twins and
        // suspends inside the property's body.
        var asyncCounter = new Counter();
        var asyncDisplay = DisplayOf(await KatLangEngine.RunAsync($"{Helpers}\n{read}\n{consumer}", AsyncTick(asyncCounter)));

        Assert.Equal(1, asyncCounter.Count);
        Assert.Equal(syncCounter.Count, asyncCounter.Count);
        Assert.Equal(syncDisplay, asyncDisplay);
    }

    /// <summary>
    /// Many different consumers of ONE ordinary property value in ONE run: builtins in both
    /// spellings, the lazy <c>if</c>, a user algorithm, a higher-order pipeline, an inline
    /// callback, a selection, and the <c>.string</c> intrinsic all share the one evaluation.
    /// </summary>
    [Fact]
    public async Task ManyConsumersInOneRun_ShareOneEvaluation()
    {
        const string rows = """
            A
            sum(A)
            A.max
            if(true, A, 0)
            Stats(A)
            A.map(Double).sum
            map(A, {x + N})
            A:1
            N.string
            Show(N)
            reduce(A, Add, N)
            """;

        var sync = new Counter();
        var syncDisplay = DisplayOf(KatLangEngine.Run($"{Helpers}\n{rows}", SyncTick(sync)));
        Assert.Equal(2, sync.Count); // A once, N once

        var asyncCounter = new Counter();
        var asyncDisplay = DisplayOf(await KatLangEngine.RunAsync($"{Helpers}\n{rows}", AsyncTick(asyncCounter)));
        Assert.Equal(2, asyncCounter.Count);
        Assert.Equal(syncDisplay, asyncDisplay);
    }

    // ── 2. The cache's own evidence: one request per consumer, one evaluation ──

    /// <summary>Run-scoped cache counting requests and ACTUAL evaluations by property name.</summary>
    private sealed class CountingCache : IAsyncZeroArgPropertyResultCache
    {
        private readonly RunScopedAsyncZeroArgPropertyResultCache _inner = new();

        public Dictionary<string, int> Requests { get; } = new(StringComparer.Ordinal);

        public Dictionary<string, int> Evaluations { get; } = new(StringComparer.Ordinal);

        public EvalResult<ZeroArgPropertyResult> GetOrEvaluate(
            ZeroArgPropertyExecution execution,
            Func<EvalResult<ZeroArgPropertyResult>> evaluate)
        {
            Count(Requests, execution.Binding.Name);
            return _inner.GetOrEvaluate(execution, () =>
            {
                Count(Evaluations, execution.Binding.Name);
                return evaluate();
            });
        }

        public ValueTask<EvalResult<ZeroArgPropertyResult>> GetOrEvaluateAsync(
            ZeroArgPropertyExecution execution,
            Func<ValueTask<EvalResult<ZeroArgPropertyResult>>> evaluateAsync)
        {
            Count(Requests, execution.Binding.Name);
            return _inner.GetOrEvaluateAsync(execution, () =>
            {
                Count(Evaluations, execution.Binding.Name);
                return evaluateAsync();
            });
        }

        private static void Count(Dictionary<string, int> counts, string name)
            => counts[name] = counts.GetValueOrDefault(name) + 1;
    }

    private static (CountingCache Cache, EvalResult<Result> Result) RunCounting(string source)
    {
        var cache = new CountingCache();
        return (cache, Evaluator.Run(new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root), cache));
    }

    [Theory]
    [InlineData("sum(A), A.sum, sum((A))")]
    [InlineData("if(true, A, 0), if(false, 0, A), if(true, (A), 0)")]
    [InlineData("take(A, 1), A.take(1), first(A)")]
    [InlineData("A.string, (A).string, A.string")]
    [InlineData("repeat(Keep, 1, A), while({s + 1, s < 9}, A), reduce([], Add, A)")]
    public void BuiltinSlots_RequestTheEntry_AndEvaluateTheBodyOnce(string consumers)
    {
        var (cache, result) = RunCounting($"A = 7\nKeep(s) = s\nAdd(e, acc) = e + acc\nA\n{consumers}");

        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        // The ordinary read plus one request per consumer; ONE evaluation serves them all.
        Assert.Equal(4, cache.Requests.GetValueOrDefault("A"));
        Assert.Equal(1, cache.Evaluations.GetValueOrDefault("A"));
    }

    // ── 3. Seeded random end-to-end: builtin versus user consumers ────────────

    private static string[] RunRows(string source, long seed)
        => DisplayOf(KatLangEngine.Run(source, new RunOptions { RandomSeed = seed }))
            .Split('\n')
            .Select(static row => row.Trim())
            .ToArray();

    private const string Draw = "randomInt(1, 1000000)";

    /// <summary>
    /// A random-backed property consumed by builtins (written and dotted), the lazy
    /// <c>if</c>, the <c>.string</c> intrinsic, and user algorithms — directly and
    /// forwarded — shows ONE draw everywhere; a trailing independent draw proves the exact
    /// stream position, so no consumer drew a hidden second value.
    /// </summary>
    [Theory]
    [InlineData(0L)]
    [InlineData(8L)]
    [InlineData(-1L)]
    [InlineData(20260927L)]
    public void RandomProperty_EveryConsumerSeesTheSameDraw(long seed)
    {
        var source = $$"""
            D = {{Draw}}
            Id(x) = x
            Show(v) = v.string
            Stats(xs) = sum(xs), max(xs)
            D
            sum(D)
            D.sum
            D.max
            if(D > 0, D, 0)
            D.string
            Id(D)
            Show(D)
            Stats(D):1
            first([D, 0])
            D.map({x}).first
            {{Draw}}
            """;

        var rows = RunRows(source, seed);
        var reference = RunRows($"{Draw}, {Draw}", seed);

        Assert.Equal(12, rows.Length);
        Assert.All(rows[..^1], row => Assert.Equal(reference[0], row));
        Assert.Equal(reference[1], rows[^1]);
    }

    // ── 4. Explicit invocation bypasses, but never mutates, the entry ─────────

    /// <summary>
    /// <c>A</c> stores; <c>A()</c> evaluates afresh WITHOUT replacing the entry; a later
    /// <c>A</c> reads the ORIGINAL value. And <c>A()</c> first populates nothing: the first
    /// ordinary read stores and the next one reuses. Explicit calls inside a builtin slot
    /// are still explicit calls.
    /// </summary>
    [Theory]
    [InlineData(0L)]
    [InlineData(8L)]
    [InlineData(20260927L)]
    public void ExplicitCall_BypassesWithoutReadingOrReplacingTheEntry(long seed)
    {
        var r = RunRows(string.Join(", ", Enumerable.Repeat(Draw, 5)), seed);

        Assert.Equal([r[0], r[1], r[0], r[2]], RunRows($"D = {Draw}\nD\nD()\nD\n{Draw}", seed));
        Assert.Equal([r[0], r[1], r[1], r[2]], RunRows($"D = {Draw}\nD()\nD\nD\n{Draw}", seed));
        Assert.Equal([r[0], r[1], r[2]], RunRows($"D = {Draw}\nD()\nD()\n{Draw}", seed));
        Assert.Equal([r[0], r[0], r[1]], RunRows($"D = {Draw}\nD\nD\n{Draw}", seed));
        // Builtin slots follow the same rule: `sum(D())` is a fresh explicit call; `D.max`
        // and `if(true, D, 0)` read the entry the first `sum(D)` stored.
        Assert.Equal([r[0], r[1], r[0], r[0], r[2]],
            RunRows($"D = {Draw}\nsum(D)\nsum(D())\nD.max\nif(true, D, 0)\n{Draw}", seed));
        // `.string` after an explicit call still converts the cached value.
        Assert.Equal([r[0], r[1], r[0]], RunRows($"D = {Draw}\nD.string\nD().string\nD.string", seed));
    }

    [Fact]
    public void ExplicitCall_CountsFreshEvaluations_WhileOrdinaryReadsShareOne()
    {
        static int Invocations(string rows)
        {
            var counter = new Counter();
            DisplayOf(KatLangEngine.Run($"P = Tick()\n{rows}", SyncTick(counter)));
            return counter.Count;
        }

        Assert.Equal(2, Invocations("P\nP()\nP"));
        Assert.Equal(2, Invocations("P()\nP\nP"));
        Assert.Equal(2, Invocations("P()\nP()"));
        Assert.Equal(1, Invocations("P\nP\nsum(P)\nP.string"));
        Assert.Equal(3, Invocations("sum(P)\nsum(P())\nP().string\nP.string"));

        // A callable forwarded through a parameter and INVOKED explicitly is an explicit
        // call: `Call0(P)` reads P's cached value for the argument and `f()` runs afresh.
        Assert.Equal(2, Invocations("Call0(f) = f()\nP\nCall0(P)\nP"));
    }

    // ── 5. Cache identity follows the resolved binding, not the spelling ─────

    /// <summary>
    /// <c>Inner</c> declares its own <c>A</c>, shadowing the root's: two bindings, two
    /// entries, two values, each evaluated once however it is consumed — and resolution
    /// returning to the root <c>A</c> finds the root's own entry.
    /// </summary>
    [Fact]
    public void ShadowingProperties_KeepSeparateEntries()
    {
        var outer = new Counter();
        var inner = new Counter();
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(
                HostOperation.Create("OuterTick", (_, _) =>
                {
                    outer.Increment();
                    return new Result.Atom(10);
                }),
                HostOperation.Create("InnerTick", (_, _) =>
                {
                    inner.Increment();
                    return new Result.Atom(20);
                })),
        };

        const string source = """
            A = OuterTick()
            Inner = {
                A = InnerTick()
                A, sum(A), A.string, if(true, A, 0)
            }
            A
            sum(A)
            Inner
            A.string
            Inner
            if(true, A, 0)
            """;

        var rows = DisplayOf(KatLangEngine.Run(source, options)).Split('\n').Select(static row => row.Trim()).ToArray();

        Assert.Equal(1, outer.Count);
        Assert.Equal(1, inner.Count);
        Assert.Equal("10", rows[0]);
        Assert.Equal("10", rows[1]);
        Assert.Equal("(20, 20, 20, 20)", rows[2]);
        Assert.Equal("10", rows[3]);
        Assert.Equal(rows[2], rows[4]);
        Assert.Equal("10", rows[5]);

        // The cache itself: one evaluation per BINDING named A, one for Inner.
        var (cache, result) = RunCounting("""
            A = 1
            Inner = {
                A = 2
                A, sum(A), if(true, A, 0)
            }
            A, sum(A), Inner, Inner, if(true, A, 0)
            """);
        Assert.False(result.IsError);
        Assert.Equal(2, cache.Evaluations.GetValueOrDefault("A"));
        Assert.Equal(1, cache.Evaluations.GetValueOrDefault("Inner"));
    }

    /// <summary>
    /// A LOCAL-ONLY property (its value reads its owner's parameter) keeps one entry per
    /// activation — separate calls never share it — while within one activation every
    /// consumer, builtin slots included, shares the one evaluation.
    /// </summary>
    [Fact]
    public void LocalOnlyProperty_SharesItsActivationEntryAcrossConsumers()
    {
        var counter = new Counter();
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(HostOperation.Create("Echo", (args, _) =>
            {
                counter.Increment();
                return args[0];
            }, "value")),
        };

        const string source = """
            Outer(x) = {
                P = Echo(x)
                P + sum(P) + if(true, P, 0) + P.string.count + max(P)
            }
            Outer(1)
            Outer(2)
            """;

        Assert.Equal($"5{Environment.NewLine}9", DisplayOf(KatLangEngine.Run(source, options)));
        Assert.Equal(2, counter.Count); // one per activation, never per consumer
    }

    // ── 6. Failed evaluations are never stored ───────────────────────────────

    /// <summary>Property-cache failures remain local to each access; only successes are stored.</summary>
    [Fact]
    public void FailedEvaluation_IsNotStored_TheFirstSuccessIs()
    {
        var root = SourceProvenance.ParseValid("Bad = 7\nBad").Root;
        var binding = Assert.Single(root.Properties);
        var execution = new ZeroArgPropertyExecution(root, binding, ZeroArgPropertyAccessKind.Lexical,
            new object(), new object(), new object(), new object());
        var cache = new RunScopedZeroArgPropertyResultCache();
        var attempts = 0;
        var failure = new EvalError.DivByZero();
        var first = cache.GetOrEvaluate(execution, () => { attempts++; return failure; });
        Assert.Same(failure, first.Error);
        var second = cache.GetOrEvaluate(execution, () => { attempts++; return EvalResult<ZeroArgPropertyResult>.Ok(new(new Result.Atom(7), 1)); });
        var third = cache.GetOrEvaluate(execution, () => throw new InvalidOperationException("a stored success was re-evaluated"));
        Assert.Equal(2, attempts);
        Assert.Same(second.Value.Value, third.Value.Value);
        Assert.Equal(1, cache.GetSnapshot().Stores);
    }

    // ── 7. Callback slots still receive the algorithm ─────────────────────────

    /// <summary>
    /// Consumer transparency concerns VALUE slots. A named callable in a CALLBACK slot is
    /// still invoked (an invocation is an explicit call), a collecting-only callback is
    /// never eagerly evaluated for a value, and an unused callback is never demanded.
    /// </summary>
    [Fact]
    public void CallbackSlots_StillInvokeTheNamedCallable()
    {
        static int Invocations(string source)
        {
            var counter = new Counter();
            DisplayOf(KatLangEngine.Run(source, SyncTick(counter)));
            return counter.Count;
        }

        // `Only` is collecting-only: as a VALUE it could be read, but in the map slot it is
        // the callback, called once per element and never read eagerly.
        Assert.Equal(2, Invocations("Only(*xs) = xs.count + Tick()\nmap([1, 2], Only)"));
        Assert.Equal(0, Invocations("Only(*xs) = xs.count + Tick()\nmap([], Only)"));
        // A loop step is CALLED once per iteration, never read as a cached value.
        Assert.Equal(3, Invocations("Step(s) = s + Tick()\nrepeat(Step, 3, 0)"));
    }
}
