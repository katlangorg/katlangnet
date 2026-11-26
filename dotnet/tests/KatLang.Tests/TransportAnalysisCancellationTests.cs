using System.Collections;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Sequences;
using KatLang.Rendering;
using CountedResult = KatLang.Evaluator.CountedResult;

namespace KatLang.Tests;

/// <summary>
/// The transport-name analysis of a per-site run (J7, <see cref="Evaluator.IsUnobservedSupplySlot"/>) runs DURING
/// evaluation and observes the run's token in bounded blocks (<see cref="Evaluator.TransportAnalysisWork"/>,
/// <see cref="FrontEndCancellationCheckpoint.EvaluatorTransportAnalysis"/>): ONE countdown across the callee walk
/// (<see cref="Evaluator.TransportedNamesOf"/>), the builtin-aware summary and the program-wide inherited-read walk
/// (<see cref="Evaluator.InheritedTransportNames"/>, its tree walk and its memoized fallback). Its units include
/// in-place edges, frame completions, argument names and properties indexed for a lookup. On main 4a156e88 the walks ran
/// to its end after the run's token was cancelled inside it: a host-built program read the remaining 1,048,566 argument
/// names of one wide native node, and walked all 65,536 members of a tree, of a shared DAG and of one callee's body
/// (and the 65,536 rows of a builtin-slot callee), on <c>Evaluator.Run</c>, <c>RunAsync</c> and the async twin alike.
///
/// <para>Every cancellation is placed by the checkpoint hook, which runs BEFORE the token is read, so the cancelling
/// checkpoint itself throws: tests assert outcomes, token identity, the walk the exception came from, checkpoint
/// ordinals and unit counts, and that nothing moved after the cancelling checkpoint — never time. A cancelled analysis
/// publishes nothing partial and is abandoned for the rest of the run. A token that is never cancelled changes no
/// value, plan, fusion, accounting, inherited name or memo. Host-only policy: Lean models no cancellation, and per-site
/// retention is a C#-only optimization.</para>
/// </summary>
public sealed class TransportAnalysisCancellationTests
{
    private const int Block = AstStructuralPreflight.CancellationCheckpointEdges;
    private const FrontEndCancellationCheckpoint Kind = FrontEndCancellationCheckpoint.EvaluatorTransportAnalysis;
    private const int Limit = EvaluationLimits.MaxSupportedAstDepth;
    private const AstConsumerProfile Profile = AstConsumerProfile.EvaluatorIterativeJoinSpines;

    // `Unused` keeps the run loop-only (per-site); `Id(Inc(1))` forms a call-shaped argument for a callee whose
    // parameter is transport-free, so its slot is classified, first by Id's body and then by the inherited-read walk.
    private const string Core = "Id(x) = x\nInc(x) = x + 1\nUnused(s) = s.while\n";

    // ── Harness ─────────────────────────────────────────────────────────────────────────────────────

    /// <summary>A token source cancelled by the observer's hook at one transport checkpoint, with the work seen there.</summary>
    private sealed class CancelAt : IDisposable
    {
        public CancelAt(long ordinal, Action<long>? onCheckpoint = null, Func<int>? resumed = null)
        {
            Observations = new FrontEndTraversalObservations
            {
                CheckpointReached = (reached, count) =>
                {
                    if (reached != Kind)
                        return;
                    onCheckpoint?.Invoke(count);
                    if (count != ordinal)
                        return;
                    WorkAtCancel = Work(Observations!);
                    ResumedAtCancel = resumed?.Invoke();
                    Source.Cancel();
                },
            };
        }

        public CancellationTokenSource Source { get; } = new();

        public CancellationToken Token => Source.Token;

        public FrontEndTraversalObservations Observations { get; }

        public long[]? WorkAtCancel { get; private set; }

        public int? ResumedAtCancel { get; private set; }

        /// <summary>Nothing ran after the cancelling checkpoint: every counter stands where the hook saw it.</summary>
        public void AssertNothingAfterTheCancellingCheckpoint()
        {
            Assert.NotNull(WorkAtCancel);
            Assert.Equal(WorkAtCancel, Work(Observations));
        }

        public void Dispose() => Source.Dispose();
    }

    private static long[] Work(FrontEndTraversalObservations observations) =>
    [
        observations.EvaluatorTransportAnalysisUnits,
        observations.CancellationCheckpoints,
        observations.CancellationCheckpointsOf(Kind),
    ];

    /// <summary>A host name list that counts its reads and cancels its token at one: the seam for public entries.</summary>
    private sealed class CountingNames(int count) : IReadOnlyList<string>
    {
        public CancellationTokenSource Source { get; } = new();

        public long Reads { get; private set; }

        public long CancelAt { get; set; } = long.MaxValue;

        public long ReadsAtCancel { get; private set; } = -1;
        public Action? OnCancel { get; init; }

        private string Read()
        {
            Reads++;
            if (Reads == CancelAt)
            {
                ReadsAtCancel = Reads;
                Source.Cancel();
                OnCancel?.Invoke();
            }
            return "a";
        }

        public int Count => count;

        public string this[int index] => Read();

        public IEnumerator<string> GetEnumerator()
        {
            for (var index = 0; index < count; index++)
                yield return Read();
        }

        IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();
    }

    /// <summary>A host list that GROWS once flipped: an unstable collection the admission saw in its first state.</summary>
    private sealed class FlipList<T>(IReadOnlyList<T> before, IReadOnlyList<T> after) : IReadOnlyList<T>
    {
        public bool Flipped { get; set; }

        private IReadOnlyList<T> Items => Flipped ? after : before;

        public int Count => Items.Count;

        public T this[int index] => Items[index];

        public IEnumerator<T> GetEnumerator() => Items.GetEnumerator();

        IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();
    }

    /// <summary>A parameter-pattern list that counts its reads: proves an abandoned analysis reads no callee.</summary>
    private sealed class CountedPatterns(IReadOnlyList<ParameterPattern> items) : IReadOnlyList<ParameterPattern>
    {
        public int Reads { get; private set; }

        public int Count
        {
            get { Reads++; return items.Count; }
        }

        public ParameterPattern this[int index]
        {
            get { Reads++; return items[index]; }
        }

        public IEnumerator<ParameterPattern> GetEnumerator()
        {
            for (var index = 0; index < items.Count; index++)
                yield return this[index];
        }

        IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();
    }

    public enum Engine { Sync, AsyncFast, Twin, TwinSuspended }

    /// <summary>The run's one host operation <c>wait()</c>: synchronous, asynchronous inline, or suspending once.</summary>
    private sealed class Wait
    {
        private int _resumed;

        public int Resumed => Volatile.Read(ref _resumed);

        public HostOperations Operations(Engine engine) => engine switch
        {
            Engine.Sync or Engine.AsyncFast => HostOperations.Create(HostOperation.Create("wait", (_, _) => new Result.Atom(0))),
            Engine.Twin => HostOperations.Create(HostOperation.CreateAsync("wait", (_, _) => ValueTask.FromResult<Result>(new Result.Atom(0)))),
            _ => HostOperations.Create(HostOperation.CreateAsync("wait", async (_, _) =>
            {
                await Task.Yield();
                Interlocked.Increment(ref _resumed);
                return new Result.Atom(0);
            })),
        };
    }

    private static async Task<(EvalResult<CountedResult> Result, EvaluationBudget Budget)> Run(
        Engine engine, Expr program, HostOperations operations, EvaluationObservations observations, CancellationToken token)
        => engine switch
        {
            Engine.Sync => Evaluator.RunCountedObserved(program, observations: observations, hostOperations: operations,
                cancellationToken: token),
            Engine.AsyncFast => await Evaluator.RunCountedObservedAsync(program, observations: observations, hostOperations: operations,
                cancellationToken: token),
            _ => await Evaluator.RunCountedObservedAsync(program, zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
                observations: observations, hostOperations: operations, cancellationToken: token),
        };

    /// <summary>A source the front end accepts, parsed with the host operations its names resolve to.</summary>
    private static Algorithm.User ParseValid(string source, HostOperations? operations)
    {
        if (operations is null)
            return SourceProvenance.ParseValid(source).Root;
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        return parsed.Root;
    }

    // ── Programs ────────────────────────────────────────────────────────────────────────────────────

    private static Property Native(string name, IReadOnlyList<string> names)
        => new(name, new Algorithm.User(null, [], [], [], [new Expr.NativeCall("wait", names)]));

    /// <summary><paramref name="width"/> distinct one-row members; with <paramref name="shared"/> they share ONE row node.</summary>
    private static IEnumerable<Property> Members(int width, bool shared = false, string row = "")
    {
        var sharedRow = new Expr.Num(7);
        return Enumerable.Range(0, width).Select(i => new Property("M" + i, new Algorithm.User(null, [], [], [],
            [row.Length > 0 ? new Expr.Param(row) : shared ? sharedRow : new Expr.Num(i % 10)])));
    }

    private static Algorithm.User WithProperties(Algorithm.User root, IEnumerable<Property> extra)
        => root with { Properties = [.. root.Properties, .. extra] };

    private static Algorithm.User WithCalleeProperties(Algorithm.User root, string callee, IEnumerable<Property> extra)
        => root with
        {
            Properties = [.. root.Properties.Select(property => property.Name != callee ? property : property with
            {
                Value = ((Algorithm.User)property.Value) with { Properties = [.. extra] },
            })],
        };

    /// <summary>
    /// The shapes, each with the walk its bulk is in. ONE WIDE NODE: <c>native</c> (one host call naming 16 blocks of
    /// arguments, which no admission walk reads) and <c>rows</c> (one body of 16 blocks of inherited parameter reads,
    /// classified in place). MANY EDGES: <c>members</c> (a tree) and <c>shared</c> (8,192 members sharing one row: a DAG
    /// walked with its memo, whose hits are edges too). CALLEE BODIES: <c>callee</c> (the members inside <c>Id</c>) and
    /// <c>builtin</c> (inside <c>F(x) = if(x > 0, x, 0)</c>, whose slot is decided by the builtin-aware summary after the
    /// callee walk).
    /// </summary>
    private static Expr Program(string shape, HostOperations operations)
    {
        var tail = shape == "builtin" ? "F(x) = if(x > 0, x, 0)\nwait() + F(Inc(1))" : "wait() + Id(Inc(1))";
        var root = ParseValid(Core + tail, operations);
        root = shape switch
        {
            "native" => WithProperties(root, [Native("Wide", Enumerable.Repeat("a", 16 * Block).ToArray())]),
            "rows" => WithProperties(root, [new Property("Rows", new Algorithm.User(null, [], [], [],
                [.. Enumerable.Repeat<Expr>(new Expr.Param("p"), 16 * Block)]))]),
            "members" => WithProperties(root, Members(8192)),
            "shared" => WithProperties(root, Members(8192, shared: true)),
            "callee" => WithCalleeProperties(root, "Id", Members(8192, row: "q")),
            "builtin" => WithCalleeProperties(root, "F", Members(8192, row: "q")),
            _ => throw new ArgumentOutOfRangeException(nameof(shape), shape, null),
        };
        return new Expr.AlgorithmExpr(root);
    }

    /// <summary>The walk each shape's cancellation is placed in (a frame of the escaping exception's stack trace).</summary>
    private static string WalkOf(string shape) => shape switch
    {
        "callee" => nameof(Evaluator.TransportedNamesOf),
        "builtin" => "CalleeBuiltinSlotSummary",
        _ => "InheritedTransportNamesCore",
    };

    private static string Outcome(EvalResult<CountedResult> result)
        => result.IsOk ? "ok " + Neutral(result.Value.Value) : $"err {result.Error.Code}: {result.Error} @ {result.Error.Span}";

    private static string Neutral(Result value) => value switch
    {
        Result.Atom atom => ValueTextRenderer.FormatNumberInvariant(atom.Value),
        Result.Str text => "'" + text.Value + "'",
        Result.Bool boolean => boolean.Value ? "true" : "false",
        Result.SequenceValue sequence => "S[" + string.Join(", ", sequence.Items.Select(Neutral)) + "]",
        Result.ListValue list => "L[" + string.Join(", ", list.Items.Select(Neutral)) + "]",
        Result.CallReference => "CallReference",
    };

    // ── Cancellation inside the analysis ────────────────────────────────────────────────────────────

    /// <summary>
    /// A cancellation requested inside the analysis stops it at the cancelling checkpoint, on the synchronous route, the
    /// async fast path, the twin path and a twin run that suspended before the analysis began: the escaping exception is
    /// the run's cancellation with its token, thrown by the analysis checkpoint inside the shape's walk (inside one wide
    /// node, across many edges, in a shared DAG, in a callee's body or its builtin-aware summary), after exactly the
    /// blocks before it, and no unit or checkpoint ran after it.
    /// </summary>
    [Theory]
    [InlineData("native", 9)]
    [InlineData("rows", 7)]
    [InlineData("members", 7)]
    [InlineData("shared", 11)]
    [InlineData("callee", 5)]
    [InlineData("builtin", 28)]
    public async Task TheAnalysis_CancelledInside_StopsAtTheCancellingCheckpoint(string shape, long ordinal)
    {
        if (ForcedInvocationPlansHook.Forced) return; // no per-site run: no analysis
        foreach (var engine in Enum.GetValues<Engine>())
        {
            var wait = new Wait();
            var operations = wait.Operations(engine);
            var program = Program(shape, operations);
            EvaluationObservations? observations = null;
            long plansAtCancellation = -1;
            using var cancel = new CancelAt(ordinal, onCheckpoint: at =>
            {
                if (at == ordinal)
                    plansAtCancellation = observations!.InvocationPlanCount;
            }, resumed: () => wait.Resumed);
            observations = new EvaluationObservations { TransportAnalysisTraversal = cancel.Observations };

            var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => Run(engine, program, operations, observations, cancel.Token));

            Assert.Equal(cancel.Token, error.CancellationToken);
            Assert.Contains(nameof(Evaluator.TransportAnalysisWork), error.StackTrace, StringComparison.Ordinal);
            Assert.Contains(WalkOf(shape), error.StackTrace, StringComparison.Ordinal);
            Assert.Equal(ordinal, cancel.Observations.CancellationCheckpointsOf(Kind));
            Assert.Equal(ordinal * Block, cancel.Observations.EvaluatorTransportAnalysisUnits);
            cancel.AssertNothingAfterTheCancellingCheckpoint();
            Assert.Equal(plansAtCancellation, observations.InvocationPlanCount);
            if (engine == Engine.TwinSuspended)
                Assert.Equal(1, cancel.ResumedAtCancel);
        }
    }

    /// <summary>
    /// The public entries take no observer, so a host argument-name list — read only by the analysis — counts the reads
    /// instead and cancels at the tenth: the walk reads at most one block more and never reaches the native node after it,
    /// where it formerly read every name (1,048,566 after the cancelling read for 2^20 names on 4a156e88) and the rest of
    /// the program.
    /// </summary>
    [Theory]
    [InlineData("Run")]
    [InlineData("RunAsync")]
    [InlineData("RunAsync(async host operations)")]
    [InlineData("RunFlatAsync")]
    public async Task PublicEntries_StopTheAnalysis_WithinOneBlockOfReads(string entry)
    {
        if (ForcedInvocationPlansHook.Forced) return;
        var wide = new CountingNames(64 * Block) { CancelAt = 10 };
        var last = new CountingNames(1);
        using var source = wide.Source;
        using var unused = last.Source;
        var root = WithProperties(ParseValid(Core + "Id(Inc(1))", operations: null), [Native("Wide", wide), Native("Last", last)]);
        var program = new Expr.AlgorithmExpr(root);
        var token = source.Token;
        var asynchronous = HostOperations.Create(HostOperation.CreateAsync("Data", (_, _) => ValueTask.FromResult<Result>(new Result.Atom(1))));

        var thrown = entry switch
        {
            "Run" => Record.Exception(() => Evaluator.Run(program, limits: null, randomSeed: null, token)),
            "RunAsync" => await Record.ExceptionAsync(() => Evaluator.RunAsync(program, null, token)),
            "RunAsync(async host operations)" => await Record.ExceptionAsync(() => Evaluator.RunAsync(program, asynchronous, null, null, token)),
            _ => await Record.ExceptionAsync(() => Evaluator.RunFlatAsync(program, null, token)),
        };

        var error = Assert.IsAssignableFrom<OperationCanceledException>(thrown);
        Assert.Equal(token, error.CancellationToken);
        Assert.Equal(10, wide.ReadsAtCancel);
        Assert.InRange(wide.Reads - wide.ReadsAtCancel, 0, Block);
        Assert.Equal(0, last.Reads);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task CancellationAtTheDeepestLeaf_StopsDuringTheFrameDrain(bool asynchronous)
    {
        if (ForcedInvocationPlansHook.Forced) return;
        var traversal = new FrontEndTraversalObservations();
        long atLeaf = 0;
        var leaf = new CountingNames(1) { CancelAt = 1, OnCancel = () => atLeaf = traversal.EvaluatorTransportAnalysisUnits };
        using var source = leaf.Source;
        Expr spine = new Expr.NativeCall("wait", leaf);
        for (var i = 0; i < 8 * Block; i++)
            spine = new Expr.SequenceSpread(spine);
        var root = WithProperties(SourceProvenance.ParseValid(Core + "Id(Inc(1))").Root,
            [new Property("Deep", new Algorithm.User(null, [], [], [], [spine]))]);
        var program = new Expr.AlgorithmExpr(root);
        var engine = asynchronous ? Engine.Twin : Engine.Sync;
        var observations = new EvaluationObservations { TransportAnalysisTraversal = traversal };
        var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(() =>
            Run(engine, program, new Wait().Operations(engine), observations, source.Token));

        Assert.Equal(source.Token, error.CancellationToken);
        Assert.Equal(1, leaf.Reads);
        Assert.Contains("InheritedTransportNamesCore", error.StackTrace, StringComparison.Ordinal);
        Assert.InRange(atLeaf, 8 * Block, long.MaxValue);
        Assert.InRange(traversal.EvaluatorTransportAnalysisUnits - atLeaf, 1, Block);
    }

    // The structural walks use the indexer. A cold name lookup uses the enumerator. Count only the selected access.
    private sealed class CountingProperties(Property[] items, CancellationTokenSource source, bool countEnumerator) : IReadOnlyList<Property>
    {
        public int Count => items.Length;
        public Property this[int i] => Read(items[i], enumerated: false);
        public bool Armed { get; set; }
        public int Reads { get; private set; }

        private Property Read(Property property, bool enumerated)
        {
            if (Armed && countEnumerator == enumerated && ++Reads == 10)
                source.Cancel();
            return property;
        }

        public IEnumerator<Property> GetEnumerator()
        {
            foreach (var property in items)
                yield return Read(property, enumerated: true);
        }
        IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task AColdBuiltinHeadIndex_StopsWithinOneBlockOfProperties(bool asynchronous)
    {
        if (ForcedInvocationPlansHook.Forced) return;
        using var source = new CancellationTokenSource();
        var properties = new CountingProperties([.. Members(8 * Block)], source, countEnumerator: true);
        var root = SourceProvenance.ParseValid(Core + "F(x) = count(x)\nF(Inc(1))").Root;
        root = root with { Properties = [.. root.Properties.Select(p => p.Name == "F"
            ? p with { Value = ((Algorithm.User)p.Value) with { Properties = properties } } : p)] };
        var traversal = new FrontEndTraversalObservations { CheckpointReached = (kind, _) => properties.Armed |= kind == Kind };
        var engine = asynchronous ? Engine.Twin : Engine.Sync;
        var observations = new EvaluationObservations { TransportAnalysisTraversal = traversal };
        var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(() =>
            Run(engine, new Expr.AlgorithmExpr(root), new Wait().Operations(engine), observations, source.Token));

        Assert.Equal(source.Token, error.CancellationToken);
        Assert.Contains(nameof(PropertyBindingIndexCache.Lookup), error.StackTrace, StringComparison.Ordinal);
        Assert.InRange(properties.Reads, 10, 10 + Block);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task InheritedReads_StopWithinOneBlockOfDistinctOrMemoizedChildEdges(bool shared)
    {
        if (ForcedInvocationPlansHook.Forced) return;
        using var source = new CancellationTokenSource();
        var members = Members(8 * Block).ToArray();
        if (shared)
            for (var i = 1; i < members.Length; i++)
                members[i] = members[i] with { Value = members[0].Value };
        var properties = new CountingProperties(members, source, countEnumerator: false);
        var owner = new Algorithm.User(null, [], [], properties, [new Expr.Num(0)]);
        var root = WithProperties(SourceProvenance.ParseValid(Core + "Id(Inc(1))").Root, [new Property("Owner", owner)]);
        var traversal = new FrontEndTraversalObservations { CheckpointReached = (kind, _) => properties.Armed |= kind == Kind };
        var observations = new EvaluationObservations { TransportAnalysisTraversal = traversal };
        var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => Run(Engine.Twin, new Expr.AlgorithmExpr(root),
            new Wait().Operations(Engine.Twin), observations, source.Token));

        Assert.Equal(source.Token, error.CancellationToken);
        Assert.Contains("InheritedTransportNamesCore", error.StackTrace, StringComparison.Ordinal);
        Assert.InRange(properties.Reads, 10, 10 + Block);
    }

    [Fact]
    public void ACancellationThrownByAHostList_AbandonsTheQueryBeforeTheNextCheckpoint()
    {
        if (ForcedInvocationPlansHook.Forced) return;
        using var cancel = new CancellationTokenSource();
        var thrown = new OperationCanceledException(cancel.Token);
        var leaf = new CountingNames(1) { CancelAt = 1, OnCancel = () => { cancel.Cancel(); throw thrown; } };
        using var listSource = leaf.Source;
        var root = WithProperties(SourceProvenance.ParseValid(Core + "Id(Inc(1))").Root, [Native("Last", leaf)]);
        var program = new Expr.AlgorithmExpr(root);
        Assert.Null(AstStructuralPreflight.CheckAdmittedProgram(program, Limit, Profile, out var facts));
        var traversal = new FrontEndTraversalObservations();
        var budget = EvaluationBudget.Create(null, cancellationToken: cancel.Token);
        budget.DecideInvocationPlanRetention(true, true, program, facts.TreeNodeCount, traversal);
        var id = root.Properties.Single(p => p.Name == "Id").Value;

        Assert.Same(thrown, Assert.Throws<OperationCanceledException>(() => Evaluator.IsUnobservedSupplySlot(id, 0, budget)));
        var beforeRetry = Work(traversal);
        Assert.Same(thrown, Assert.Throws<OperationCanceledException>(() => Evaluator.IsUnobservedSupplySlot(id, 0, budget)));
        Assert.Equal(beforeRetry, Work(traversal));
        Assert.Equal(1, leaf.Reads);
        Assert.Equal(0, traversal.CancellationCheckpoints);
        Assert.Null(budget.InheritedTransportNames);
    }

    // ── A token that is never cancelled ─────────────────────────────────────────────────────────────

    public static TheoryData<string> LiveShapes => new() { "native", "rows", "members", "shared", "callee", "builtin" };

    /// <summary>
    /// A token that is never cancelled changes nothing the run computes: the same value, plans, accounting, inherited
    /// names and memo sizes as a run without a token, on the synchronous and the twin route; the observer counts the same
    /// units with or without the token, one checkpoint per block only with it. A run with neither a cancellable token nor
    /// an observer allocates no countdown at all.
    /// </summary>
    [Theory]
    [MemberData(nameof(LiveShapes))]
    public async Task ALiveToken_ChangesNoTransportFactPlanOrResult(string shape)
    {
        if (ForcedInvocationPlansHook.Forced) return;
        foreach (var engine in new[] { Engine.Sync, Engine.Twin })
        {
            var operations = new Wait().Operations(engine);
            var program = Program(shape, operations);
            var plain = await Observe(engine, program, operations, transport: null, CancellationToken.None);
            var counted = new FrontEndTraversalObservations();
            var observed = await Observe(engine, program, operations, counted, CancellationToken.None);
            using var live = new CancellationTokenSource();
            var liveCounted = new FrontEndTraversalObservations();
            var withToken = await Observe(engine, program, operations, liveCounted, live.Token);

            Assert.Equal("ok 2", plain.Outcome);
            Assert.Equal(plain, observed with { HasCountdown = false });
            Assert.Equal(plain, withToken with { HasCountdown = false });
            Assert.False(plain.HasCountdown);
            Assert.True(observed.HasCountdown);
            Assert.True(withToken.HasCountdown);
            Assert.Equal(counted.EvaluatorTransportAnalysisUnits, liveCounted.EvaluatorTransportAnalysisUnits);
            Assert.InRange(counted.EvaluatorTransportAnalysisUnits, 16 * Block, long.MaxValue);
            Assert.Equal(0, counted.CancellationCheckpoints);
            Assert.Equal(liveCounted.EvaluatorTransportAnalysisUnits / Block, liveCounted.CancellationCheckpointsOf(Kind));
            Assert.Equal(liveCounted.CancellationCheckpointsOf(Kind), liveCounted.CancellationCheckpoints);
        }
    }

    private sealed record Observation(string Outcome, string Accounting, long Plans, string Inherited, int NodeMemo, long CalleeMemo, bool HasCountdown);

    private static async Task<Observation> Observe(
        Engine engine, Expr program, HostOperations operations, FrontEndTraversalObservations? transport, CancellationToken token)
    {
        var observations = new EvaluationObservations { TransportAnalysisTraversal = transport };
        var (result, budget) = await Run(engine, program, operations, observations, token);
        Assert.True(budget.UsesPerSiteInvocationPlans);
        var accounting = $"steps={budget.ConsumedSteps} checkpoints={budget.ConsumedExpressionCheckpoints} depth={budget.PeakDepth} "
            + $"items={budget.MaterializedItems} chars={budget.MaterializedStringChars}";
        var inherited = budget.InheritedTransportNames is { } names
            ? names.IsAll ? "all" : string.Join(",", names.KnownNames.Order(StringComparer.Ordinal))
            : "none";
        return new Observation(Outcome(result), accounting, observations.InvocationPlanCount, inherited,
            budget.TransportedNames.Count, budget.CalleeTransportedNames.AddedCount, budget.TransportAnalysisWork is not null);
    }

    /// <summary>
    /// Plan retention and behavior are unchanged by a live token on programs whose cells reach a loop step and on a
    /// value-only callee whose supplied pipeline fuses: the same value, plans, fusions and accounting on every engine.
    /// </summary>
    [Theory]
    [InlineData("Step(x) = x + 1, x < 3\nW(step) = while(step)\nW(Step(0))", "ok 3")]
    [InlineData("Step(x) = x + 1, x < 3\nRun(s) = { G = s.while\nG }\nRun(Step(0))", "ok 3")]
    [InlineData("Inc(x) = x + 1\nL(0, s) = 0\nL(n, s) = repeat(s, n)\nL(3, Inc(0))", "ok 3")]
    [InlineData("Id(x) = x\nUnused(s) = s.while\nId(count(filter(range(1, 10), {v > 2})))", "ok 8")]
    [InlineData("F(xs) = count(xs)\nUnused(s) = s.while\nF(filter(range(1, 10), {v > 2}))", "ok 8")]
    public async Task ALiveToken_KeepsPlanRetentionAndFusion(string source, string expected)
    {
        foreach (var engine in new[] { Engine.Sync, Engine.AsyncFast, Engine.Twin })
        {
            var operations = new Wait().Operations(engine);
            var program = new Expr.AlgorithmExpr(ParseValid(source, operations));
            var plain = await Retention(engine, program, operations, CancellationToken.None);
            using var live = new CancellationTokenSource();
            var withToken = await Retention(engine, program, operations, live.Token);
            Assert.Equal(expected, plain.Outcome);
            Assert.Equal(plain, withToken);
        }
    }

    private static async Task<(string Outcome, string Accounting, long Plans, long Fusions, bool PerSite)> Retention(
        Engine engine, Expr program, HostOperations operations, CancellationToken token)
    {
        var observations = new EvaluationObservations();
        var sequences = new SequencePipelineDiagnostics();
        var (result, budget) = engine switch
        {
            Engine.Sync => Evaluator.RunCountedObserved(program, sequenceDiagnostics: sequences, observations: observations,
                hostOperations: operations, cancellationToken: token),
            Engine.AsyncFast => await Evaluator.RunCountedObservedAsync(program, sequenceDiagnostics: sequences,
                observations: observations, hostOperations: operations, cancellationToken: token),
            _ => await Evaluator.RunCountedObservedAsync(program, zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
                sequenceDiagnostics: sequences, observations: observations, hostOperations: operations, cancellationToken: token),
        };
        var accounting = $"steps={budget.ConsumedSteps} checkpoints={budget.ConsumedExpressionCheckpoints} depth={budget.PeakDepth}";
        return (Outcome(result), accounting, observations.InvocationPlanCount, sequences.FilterCountFusionHits,
            budget.UsesPerSiteInvocationPlans);
    }

    // ── Tree, memoized fallback and unstable host graphs ────────────────────────────────────────────

    /// <summary>
    /// The countdown changes no inherited name: the tree walk, the memoized walk and the fallback after an aborted tree
    /// walk (an admitted count smaller than the graph, as an unstable host collection presents it) agree with and without
    /// it, on a tree, a shared DAG and one wide node. The fallback continues the SAME countdown: its units add to the
    /// aborted attempt's, and a cancellation placed beyond the attempt stops inside the fallback within one block.
    /// </summary>
    [Theory]
    [InlineData("members")]
    [InlineData("shared")]
    [InlineData("native")]
    public void TheTreeAndMemoizedWalks_AgreeUnderTheCountdown_AndTheFallbackContinuesIt(string shape)
    {
        var program = Program(shape, new Wait().Operations(Engine.Sync));
        Assert.Null(AstStructuralPreflight.CheckAdmittedProgram(program, Limit, Profile, out var facts));
        Assert.Equal(shape == "shared", facts.TreeNodeCount == 0);
        var expected = Evaluator.InheritedTransportNames(program);

        using var live = new CancellationTokenSource();
        var memoUnits = new FrontEndTraversalObservations();
        AssertSameNames(expected, Evaluator.InheritedTransportNames(program, 0, new Evaluator.TransportAnalysisWork(memoUnits, live.Token)));
        var treeUnits = new FrontEndTraversalObservations();
        AssertSameNames(expected, Evaluator.InheritedTransportNames(program, facts.TreeNodeCount,
            new Evaluator.TransportAnalysisWork(treeUnits, live.Token)));
        // On a tree, the tree walk follows exactly the memoized walk's edges; on a DAG the count is 0 and it IS that walk.
        Assert.Equal(memoUnits.EvaluatorTransportAnalysisUnits, treeUnits.EvaluatorTransportAnalysisUnits);

        // An admitted count of half the graph: the tree walk aborts and the memoized walk runs after it, same countdown.
        var count = Math.Max(2, facts.NodeCount / 2);
        var fallbackUnits = new FrontEndTraversalObservations();
        AssertSameNames(expected, Evaluator.InheritedTransportNames(program, count, new Evaluator.TransportAnalysisWork(fallbackUnits, live.Token)));
        var attempt = fallbackUnits.EvaluatorTransportAnalysisUnits - memoUnits.EvaluatorTransportAnalysisUnits;
        Assert.InRange(attempt, 1, memoUnits.EvaluatorTransportAnalysisUnits);
        Assert.Equal(fallbackUnits.EvaluatorTransportAnalysisUnits / Block, fallbackUnits.CancellationCheckpointsOf(Kind));

        var ordinal = attempt / Block + 2;
        Assert.InRange(ordinal * Block, attempt + 1, fallbackUnits.EvaluatorTransportAnalysisUnits);
        using var cancel = new CancelAt(ordinal);
        var error = Assert.ThrowsAny<OperationCanceledException>(() => Evaluator.InheritedTransportNames(
            program, count, new Evaluator.TransportAnalysisWork(cancel.Observations, cancel.Token)));
        Assert.Equal(cancel.Token, error.CancellationToken);
        Assert.Equal(ordinal * Block, cancel.Observations.EvaluatorTransportAnalysisUnits);
        cancel.AssertNothingAfterTheCancellingCheckpoint();
    }

    private static void AssertSameNames(Evaluator.TransportNames expected, Evaluator.TransportNames actual)
    {
        Assert.Equal(expected.IsAll, actual.IsAll);
        Assert.Equal(expected.KnownNames.Order(StringComparer.Ordinal), actual.KnownNames.Order(StringComparer.Ordinal));
    }

    /// <summary>
    /// An UNSTABLE host graph in a run: a member's property list grows after admission (flipped at the analysis' first
    /// checkpoint, before the tree walk reaches it), so the tree walk outgrows the admitted count and the memoized
    /// fallback walks the grown graph. A live run still answers 2 and publishes the fallback's names, after more units
    /// than the stable control; a cancellation placed beyond everything the tree attempt can do stops in the fallback.
    /// </summary>
    [Fact]
    public async Task AnUnstableHostGraph_FallsBackUnderTheSameCountdown()
    {
        if (ForcedInvocationPlansHook.Forced) return;
        Property[] grown = [.. Members(2 * Block)];
        (Expr Program, FlipList<Property> Rows) Build()
        {
            var rows = new FlipList<Property>([], grown);
            var root = WithProperties(ParseValid(Core + "Id(Inc(1))", operations: null),
                [.. Members(4096), new Property("Grow", new Algorithm.User(null, [], [], rows, [new Expr.Num(1)]))]);
            return (new Expr.AlgorithmExpr(root), rows);
        }

        var stable = Build();
        var stableUnits = new FrontEndTraversalObservations();
        using (var live = new CancellationTokenSource())
        {
            var (result, _) = Evaluator.RunCountedObserved(stable.Program,
                observations: new EvaluationObservations { TransportAnalysisTraversal = stableUnits }, cancellationToken: live.Token);
            Assert.Equal("ok 2", Outcome(result));
        }
        Assert.InRange(stableUnits.EvaluatorTransportAnalysisUnits, 16 * Block, 17 * Block);

        var unstable = Build();
        using var flips = new CancelAt(long.MaxValue, onCheckpoint: count => unstable.Rows.Flipped |= count == 1);
        var (grownResult, budget) = Evaluator.RunCountedObserved(unstable.Program,
            observations: new EvaluationObservations { TransportAnalysisTraversal = flips.Observations }, cancellationToken: flips.Token);
        Assert.Equal("ok 2", Outcome(grownResult));
        Assert.True(unstable.Rows.Flipped);
        AssertSameNames(Evaluator.InheritedTransportNames(unstable.Program), budget.InheritedTransportNames!.Value);
        // The aborted attempt plus a memoized walk of the grown graph: more than twice the stable walk.
        Assert.InRange(flips.Observations.EvaluatorTransportAnalysisUnits, 2 * stableUnits.EvaluatorTransportAnalysisUnits, long.MaxValue);

        var cancelled = Build();
        var ordinal = flips.Observations.CancellationCheckpointsOf(Kind) - 1;
        // The memo walk alone has more than one block. This checkpoint must follow the aborted tree attempt.
        Assert.InRange(ordinal * Block, stableUnits.EvaluatorTransportAnalysisUnits + 4 * Block, long.MaxValue);
        using var cancel = new CancelAt(ordinal, onCheckpoint: count => cancelled.Rows.Flipped |= count == 1);
        var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(async () => await Evaluator.RunCountedObservedAsync(
            cancelled.Program, zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
            observations: new EvaluationObservations { TransportAnalysisTraversal = cancel.Observations }, cancellationToken: cancel.Token));
        Assert.Equal(cancel.Token, error.CancellationToken);
        Assert.Contains("InheritedTransportNamesCore", error.StackTrace, StringComparison.Ordinal);
        Assert.Equal(ordinal * Block, cancel.Observations.EvaluatorTransportAnalysisUnits);
        cancel.AssertNothingAfterTheCancellingCheckpoint();
    }

    // ── Publication, abandonment and precedence ─────────────────────────────────────────────────────

    private static (Expr Program, Algorithm.User Id, int TreeNodeCount) Admitted(string shape)
    {
        var program = Program(shape, new Wait().Operations(Engine.Sync));
        Assert.Null(AstStructuralPreflight.CheckAdmittedProgram(program, Limit, Profile, out var facts));
        var root = (Algorithm.User)((Expr.AlgorithmExpr)program).Algorithm;
        var id = (Algorithm.User)root.Properties.Single(static property => property.Name == "Id").Value;
        return (program, id, facts.TreeNodeCount);
    }

    private static EvaluationBudget PerSiteBudget(Expr program, int treeNodeCount, CancelAt cancel)
    {
        var budget = EvaluationBudget.Create(null, cancellationToken: cancel.Token);
        budget.DecideInvocationPlanRetention(programMayCapture: true, loopOnly: true, program, treeNodeCount, cancel.Observations);
        Assert.True(budget.UsesPerSiteInvocationPlans);
        return budget;
    }

    /// <summary>
    /// A cancelled analysis publishes nothing partial: cancelled in the callee walk, it leaves no callee entry and no
    /// inherited names, and every node it memoized is complete (a fresh walk of it computes the same names); cancelled in
    /// the inherited walk, the run's inherited names stay unpublished. It is ABANDONED: the next query rethrows the same
    /// exception object without reading its callee or doing any unit.
    /// </summary>
    [Theory]
    [InlineData("callee", 5)]
    [InlineData("members", 3)]
    public void ACancelledAnalysis_PublishesNothingPartial_AndIsAbandoned(string shape, long ordinal)
    {
        if (ForcedInvocationPlansHook.Forced) return; // a forced seam keeps every budget fully retaining
        var (program, id, treeNodeCount) = Admitted(shape);
        using var cancel = new CancelAt(ordinal);
        var budget = PerSiteBudget(program, treeNodeCount, cancel);

        var error = Assert.ThrowsAny<OperationCanceledException>(() => Evaluator.IsUnobservedSupplySlot(id, 0, budget));

        Assert.Equal(cancel.Token, error.CancellationToken);
        Assert.Contains(WalkOf(shape), error.StackTrace, StringComparison.Ordinal);
        Assert.Null(budget.InheritedTransportNames);
        Assert.Equal(shape == "callee" ? 0 : 1, budget.CalleeTransportedNames.AddedCount);
        if (shape == "callee")
            Assert.InRange(budget.TransportedNames.Count, 1, 8192);
        foreach (var (node, names) in budget.TransportedNames)
            AssertSameNames(Evaluator.TransportedNamesOf(node, EvaluationBudget.Create(null)), names);

        var patterns = new CountedPatterns([new CaptureParameterPattern("x")]);
        var other = new Algorithm.User(null, patterns, [], [], [new Expr.Param("x")]);
        var again = Assert.ThrowsAny<OperationCanceledException>(() => Evaluator.IsUnobservedSupplySlot(other, 0, budget));
        Assert.Same(error, again);
        Assert.Equal(0, patterns.Reads);
        cancel.AssertNothingAfterTheCancellingCheckpoint();
    }

    /// <summary>
    /// Inside an async twin run's boundary the analysis carries its cancellation: the null decision ends formation
    /// with the marker before creating the cell. Later queries report the same termination without work,
    /// and the boundary rethrows the very exception the analysis checkpoint threw. A host termination retained FIRST
    /// stays the run's outcome: the analysis' later cancellation does not replace it.
    /// </summary>
    [Fact]
    public void InsideTheTwinBoundary_TheCancellationIsCarried_AndTheFirstOutcomeWins()
    {
        if (ForcedInvocationPlansHook.Forced) return;
        var (program, id, treeNodeCount) = Admitted("members");
        using (var cancel = new CancelAt(2))
        {
            var budget = PerSiteBudget(program, treeNodeCount, cancel);
            budget.OpenHostTerminationBoundary();
            Assert.Null(Evaluator.IsUnobservedSupplySlot(id, 0, budget));
            Assert.True(cancel.Token.IsCancellationRequested);
            Assert.True(budget.CheckContinuation()?.IsHostTermination);
            Assert.Null(Evaluator.IsUnobservedSupplySlot(id, 0, budget));
            cancel.AssertNothingAfterTheCancellingCheckpoint();
            budget.CloseHostTerminationBoundary();
            var rethrown = Assert.ThrowsAny<OperationCanceledException>(budget.RethrowHostTermination);
            Assert.Equal(cancel.Token, rethrown.CancellationToken);
            Assert.Contains(nameof(Evaluator.TransportAnalysisWork), rethrown.StackTrace, StringComparison.Ordinal);
            Assert.Null(budget.InheritedTransportNames);
        }

        using (var cancel = new CancelAt(2))
        {
            var budget = PerSiteBudget(program, treeNodeCount, cancel);
            budget.OpenHostTerminationBoundary();
            var host = new InvalidOperationException("The host operation failed first.");
            Assert.True(budget.RetainHostTermination(host).IsHostTermination);
            Assert.Null(Evaluator.IsUnobservedSupplySlot(id, 0, budget));
            Assert.Equal(2, cancel.Observations.CancellationCheckpointsOf(Kind));
            budget.CloseHostTerminationBoundary();
            Assert.Same(host, Assert.Throws<InvalidOperationException>(budget.RethrowHostTermination));
        }
    }

    /// <summary>
    /// Precedence around the analysis is unchanged. An error the run reaches before any analysis keeps its outcome under
    /// a cancellable token, and a cancellation inside the analysis outranks an error the run would only reach after it.
    /// A fully retaining (seam-forced) run and a per-site run recorded without a program never start the program-wide
    /// walk: no unit, no checkpoint.
    /// </summary>
    [Fact]
    public void ErrorAndConfigurationPrecedence_AroundTheAnalysis()
    {
        if (ForcedInvocationPlansHook.Forced) return;
        var operations = new Wait().Operations(Engine.Sync);
        Expr Wide(string tail) => new Expr.AlgorithmExpr(WithProperties(ParseValid(Core + tail, operations), Members(8192)));

        using (var cancel = new CancelAt(1))
        {
            var (result, _) = Evaluator.RunCountedObserved(Wide("1 / 0 + Id(Inc(1))"),
                observations: new EvaluationObservations { TransportAnalysisTraversal = cancel.Observations },
                hostOperations: operations, cancellationToken: cancel.Token);
            Assert.True(result.IsError);
            Assert.Equal(KatLangErrorCode.DivisionByZero, result.Error.Code);
            Assert.Equal(0, cancel.Observations.EvaluatorTransportAnalysisUnits);
            Assert.False(cancel.Token.IsCancellationRequested);
        }

        using (var live = new CancellationTokenSource())
        {
            var units = new FrontEndTraversalObservations();
            var (result, _) = Evaluator.RunCountedObserved(Wide("Id(Inc(1)) + 1 / 0"),
                observations: new EvaluationObservations { TransportAnalysisTraversal = units }, hostOperations: operations,
                cancellationToken: live.Token);
            Assert.True(result.IsError);
            Assert.Equal(KatLangErrorCode.DivisionByZero, result.Error.Code);
            Assert.InRange(units.CancellationCheckpointsOf(Kind), 2, long.MaxValue);
        }

        using (var cancel = new CancelAt(2))
        {
            var error = Assert.ThrowsAny<OperationCanceledException>(() => Evaluator.RunCountedObserved(Wide("Id(Inc(1)) + 1 / 0"),
                observations: new EvaluationObservations { TransportAnalysisTraversal = cancel.Observations },
                hostOperations: operations, cancellationToken: cancel.Token));
            Assert.Equal(cancel.Token, error.CancellationToken);
            cancel.AssertNothingAfterTheCancellingCheckpoint();
        }

        using (var cancel = new CancelAt(1))
        using (InvocationPlanTestSeam.Activate(new InvocationPlanTestSeam()))
        {
            var (result, budget) = Evaluator.RunCountedObserved(Wide("Id(Inc(1))"),
                observations: new EvaluationObservations { TransportAnalysisTraversal = cancel.Observations },
                hostOperations: operations, cancellationToken: cancel.Token);
            Assert.Equal("ok 2", Outcome(result));
            Assert.False(budget.UsesPerSiteInvocationPlans);
            Assert.Equal(0, cancel.Observations.EvaluatorTransportAnalysisUnits);
            Assert.Equal(0, cancel.Observations.CancellationCheckpoints);
        }

        var (_, id, _) = Admitted("members");
        using (var cancel = new CancelAt(1))
        {
            var budget = EvaluationBudget.Create(null, cancellationToken: cancel.Token);
            budget.DecideInvocationPlanRetention(programMayCapture: true, loopOnly: true, admittedProgram: null,
                transportObservations: cancel.Observations);
            Assert.False(Evaluator.IsUnobservedSupplySlot(id, 0, budget));
            Assert.Null(budget.InheritedTransportNames);
            Assert.InRange(cancel.Observations.EvaluatorTransportAnalysisUnits, 1, Block - 1);
            Assert.False(cancel.Token.IsCancellationRequested);
        }
    }
}
