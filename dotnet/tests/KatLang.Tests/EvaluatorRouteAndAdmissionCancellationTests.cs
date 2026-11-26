using System.Numerics;
using System.Runtime.CompilerServices;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

/// <summary>
/// The evaluator's remaining unobserved walks observe the run's cancellation token in bounded blocks (follow-up of the
/// preflight cancellation of <c>EvaluatorPreflightCancellationTests</c>): the route-selection walk
/// (<see cref="DeferredModuleRegion.RequiresAsyncEvaluationCounting"/> behind <see cref="Evaluator.TreeRouteFact.Decide"/>
/// and the synchronous entry's guard; <see cref="FrontEndCancellationCheckpoint.EvaluatorRoute"/>), the validation walk
/// below its algorithm expansions (<see cref="FrontEndCancellationCheckpoint.EvaluatorValidationBlock"/>), and each
/// deferred-body admission during evaluation — the prefix accounting, the body check and its rejection replay
/// (<see cref="DeferredBodyAdmission"/>; <see cref="FrontEndCancellationCheckpoint.EvaluatorDeferredAdmission"/>). On
/// current main before this change a 65,536-member route walk ran 131,066 further list reads after its token was
/// cancelled, a 65,536-link body was validated to its end under one algorithm checkpoint, and an admission walked a whole
/// materialized body (160,005 edges for an 80,000-member module) with no token at all.
///
/// <para>Every cancellation is placed by the checkpoint hook, which runs BEFORE the token is read, so the cancelling
/// checkpoint itself throws: tests assert outcomes, token identity, checkpoint ordinals and edge or unit counts, and that
/// no counter moved after the cancelling checkpoint — never time. A token that is never cancelled changes no verdict,
/// fact, count or result. The one route walk left unobserved is the route rule's own walk for an internal caller that
/// supplies a synchronous-only cache with no decided fact: it decides the cache-pairing guard, which fails loud even under
/// a cancelled token. Host-only policy: Lean has no cancellation.</para>
/// </summary>
public sealed class EvaluatorRouteAndAdmissionCancellationTests
{
    private const int Block = AstStructuralPreflight.CancellationCheckpointEdges;
    private const int Limit = EvaluationLimits.MaxSupportedAstDepth;
    private const AstConsumerProfile Profile = AstConsumerProfile.EvaluatorIterativeJoinSpines;
    private const string Url = "https://katlang.org/cancellation/wide.kat";

    private const string SynchronousDeferredRegionMessage =
        "The program contains conditional branches whose module dependencies load on demand " +
        "(deferred module regions), which a synchronous evaluation entry point cannot await. " +
        "Use RunAsync (or an async KatLangEngine entry point).";

    private const string DeferredRegionCachePairingMessage =
        "A program with deferred module regions (conditional branches whose module dependencies load " +
        "on demand) requires an async-capable zero-argument property result cache for the run; use an " +
        "async evaluation entry point that constructs one.";

    // ── Harness ─────────────────────────────────────────────────────────────────────────────────────

    /// <summary>A token source cancelled by the observer's hook at one checkpoint, with the work counters seen there.</summary>
    private sealed class CancelAt : IDisposable
    {
        public CancelAt(FrontEndCancellationCheckpoint kind, long ordinal)
        {
            Observations = new FrontEndTraversalObservations
            {
                CheckpointReached = (reached, count) =>
                {
                    if (reached != kind || count != ordinal)
                        return;
                    WorkAtCancel = Work(Observations!);
                    Source.Cancel();
                },
            };
        }

        public CancellationTokenSource Source { get; } = new();

        public CancellationToken Token => Source.Token;

        public FrontEndTraversalObservations Observations { get; }

        public long[]? WorkAtCancel { get; private set; }

        /// <summary>Nothing ran after the cancelling checkpoint: every work counter stands where the hook saw it.</summary>
        public void AssertNothingAfterTheCancellingCheckpoint()
        {
            Assert.NotNull(WorkAtCancel);
            Assert.Equal(WorkAtCancel, Work(Observations));
        }

        public void Dispose() => Source.Dispose();
    }

    private static long[] Work(FrontEndTraversalObservations observations) =>
    [
        observations.EvaluatorRouteEdges,
        observations.StructuralPreflightEdges,
        observations.DeferredRegionPrefixEdges,
        observations.WalkerSteps,
        observations.PreEvaluationMetaPlacementSlots,
        observations.CancellationCheckpoints,
    ];

    /// <summary>Counts reads of a host list and cancels its token at a chosen read: the seam for entries that take no observer.</summary>
    private sealed class CancellingList<T>(IReadOnlyList<T> items) : IReadOnlyList<T>
    {
        public CancellationTokenSource Source { get; } = new();

        public long Reads { get; private set; }

        public long CancelAt { get; set; } = long.MaxValue;

        public long ReadsAtCancel { get; private set; } = -1;

        private void Read()
        {
            Reads++;
            if (Reads != CancelAt)
                return;
            ReadsAtCancel = Reads;
            Source.Cancel();
        }

        public int Count
        {
            get { Read(); return items.Count; }
        }

        public T this[int index]
        {
            get { Read(); return items[index]; }
        }

        public IEnumerator<T> GetEnumerator()
        {
            for (var index = 0; index < items.Count; index++)
            {
                Read();
                yield return items[index];
            }
        }

        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();
    }

    private static HostOperations SynchronousOperations() =>
        HostOperations.Create(HostOperation.Create("Data", (_, _) => new Result.Atom(1)));

    private static HostOperations AsynchronousOperations() =>
        HostOperations.Create(HostOperation.CreateAsync("Data", (_, _) => ValueTask.FromResult<Result>(new Result.Atom(1))));

    // ── Programs ────────────────────────────────────────────────────────────────────────────────────

    /// <summary><paramref name="width"/> members sharing ONE output node: a DAG whose revisits are edges too.</summary>
    private static IEnumerable<Property> SharedMembers(int width, string prefix = "P")
    {
        var shared = new Expr.Num(7);
        return Enumerable.Range(0, width).Select(i => new Property($"{prefix}{i}", new Algorithm.User(null, [], [], [], [shared])));
    }

    private static Expr Members(int width)
        => new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [.. SharedMembers(width)], [new Expr.Num(1)]));

    /// <summary>ONE body of <paramref name="width"/> rows: a single node with that many children.</summary>
    private static Expr Rows(int width)
        => new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [], [.. Enumerable.Range(0, width).Select(i => (Expr)new Expr.Num(i % 10))]));

    /// <summary>One comparison chain of <paramref name="width"/> links in one row of one body.</summary>
    private static Expr Links(int width)
        => new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [], [new Expr.Comparison(new Expr.Num(0),
            [.. Enumerable.Range(0, width).Select(i => new ComparisonLink(ComparisonOp.Lt, new Expr.Num(i + 1)))])]));

    /// <summary>A zero-weight spread chain: one row, one leaf, <paramref name="width"/> join nodes unwound by one loop.</summary>
    private static Expr SpreadChain(int width)
    {
        Expr chain = new Expr.Num(1);
        for (var i = 0; i < width; i++)
            chain = new Expr.SequenceSpread(chain);
        return new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [], [chain]));
    }

    /// <summary>A family of <paramref name="width"/> literal clauses (the last one <paramref name="mismatched"/> in arity).</summary>
    private static Expr Clauses(int width, bool mismatched = false)
    {
        var branches = Enumerable.Range(0, width).Select(i => new CondBranch(
            mismatched && i == width - 1
                ? new Pattern.SequenceValue([new Pattern.Bind("x"), new Pattern.Bind("y")])
                : new Pattern.LitInt(i),
            new Algorithm.User(null, [], [], [], [new Expr.Num(i % 10)]))).ToArray();
        return new Expr.AlgorithmExpr(new Algorithm.User(null, [], [],
            [new Property("F", new Algorithm.Conditional(null, [], branches))],
            [new Expr.Call(new Expr.Resolve("F"), new OutputBundle([new Expr.Num(0)]))]));
    }

    /// <summary>One algorithm declaring <paramref name="width"/> parameters.</summary>
    private static Expr Parameters(int width)
    {
        ParameterPattern[] patterns = [.. Enumerable.Range(0, width).Select(i => new CaptureParameterPattern($"p{i}"))];
        return new Expr.AlgorithmExpr(new Algorithm.User(null, [], [],
            [new Property("P", new Algorithm.User(null, patterns, [], [], [new Expr.Param("p0")]))], [new Expr.Num(1)]));
    }

    /// <summary>A wide body whose violation is its last row: an algorithm with a parameter and no output.</summary>
    private static Expr RowsEndingInAViolation(int width)
        => new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [],
        [
            .. Enumerable.Range(0, width).Select(i => (Expr)new Expr.Num(i % 10)),
            new Expr.AlgorithmExpr(new Algorithm.User(null, [new CaptureParameterPattern("x")], [], [], [])),
        ]));

    private static Expr Program(string shape) => shape switch
    {
        "members" => Members(8192),
        "rows" => Rows(16384),
        "links" => Links(8192),
        "spread" => SpreadChain(8192),
        "clauses" => Clauses(4096),
        "parameters" => Parameters(4096),
        "rows-violation" => RowsEndingInAViolation(8192),
        "clauses-mismatch" => Clauses(4096, mismatched: true),
        _ => throw new ArgumentOutOfRangeException(nameof(shape), shape, null),
    };

    /// <summary>
    /// A host-built root holding a deferred placeholder and <paramref name="width"/> shared members. The route walk pushes a
    /// node's children in order and pops the LAST pushed first, so a placeholder declared first beside the members is
    /// reached after all of them (<paramref name="reachedLast"/>); declared after ONE property holding the members, it is
    /// the walk's third edge.
    /// </summary>
    private static (Expr Root, DeferredModuleRegion Region) HostDeferredRoot(
        int width, bool reachedLast = true, Func<IReadOnlyList<Property>, IReadOnlyList<Property>>? wrap = null)
    {
        var raw = new Algorithm.User(null, [], [], [], [new Expr.Num(1)]);
        var loader = new ModuleLoader(new DiagnosticBag(), (_, _) => ValueTask.FromResult("public X = 1"));
        var region = new DeferredModuleRegion(loader, raw, ModuleLoader.LoadContext.PropertyDef, 0, 0, null, []);
        var placeholder = new Property("F", raw with { DeferredRegion = region });
        Property[] properties = reachedLast
            ? [placeholder, .. SharedMembers(width)]
            : [new Property("Members", new Algorithm.User(null, [], [], [.. SharedMembers(width)], [new Expr.Num(1)])), placeholder];
        return (new Expr.AlgorithmExpr(raw with { Properties = wrap is null ? properties : wrap(properties) }), region);
    }

    private static long RouteEdges(Expr program)
    {
        var observations = new FrontEndTraversalObservations();
        DeferredModuleRegion.RequiresAsyncEvaluationCounting(program, out _, observations: observations);
        return observations.EvaluatorRouteEdges;
    }

    // Every child is a distinct leaf list. The first Count read happens AFTER their parent
    // pushed them all. Draining that stack follows no more child edges.
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void CancellationWhileDrainingWideLeafStacksIsBounded(bool prefixWalk)
    {
        var empty = new CancellingList<Pattern>([]);
        using var source = empty.Source;
        var leaves = Enumerable.Range(0, 16 * Block).Select(_ => (Pattern)new Pattern.ListValue(empty)).ToArray();
        var branch = new CondBranch(new Pattern.SequenceValue(leaves), new Algorithm.User(null, [], [], [], []));
        var root = new Expr.AlgorithmExpr(new Algorithm.Conditional(null, [], [branch]));
        empty.CancelAt = empty.Reads + 1;
        var error = Assert.ThrowsAny<OperationCanceledException>(() =>
        {
            if (prefixWalk)
                AstStructuralPreflight.AccumulateDeferredRegionPrefixes(root, 0, Profile,
                    new(ReferenceEqualityComparer.Instance), new(ReferenceEqualityComparer.Instance), cancellationToken: source.Token);
            else
                Evaluator.TreeRouteFact.Decide(root, cancellationToken: source.Token);
        });
        Assert.Equal(source.Token, error.CancellationToken);
        Assert.InRange(empty.Reads - empty.ReadsAtCancel, 0, Block);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void CancellationDuringOneWidePatternScanIsBounded(bool clause)
    {
        var patterns = new CancellingList<ParameterPattern>(
            [.. Enumerable.Repeat<ParameterPattern>(new CaptureParameterPattern("x"), 16 * Block)]);
        var head = new CancellingList<Pattern>([.. Enumerable.Repeat<Pattern>(new Pattern.Bind("x"), 16 * Block)]);
        using var parameterSource = patterns.Source;
        using var headSource = head.Source;
        var body = new Algorithm.User(null, [], [], [], [new Expr.Num(1)]);
        var root = new Expr.AlgorithmExpr(clause
            ? new Algorithm.Conditional(null, [], [new CondBranch(new Pattern.SequenceValue(head), body)])
            : body with { ParameterPatterns = [new ListValueParameterPattern(patterns)] });
        head.CancelAt = head.Reads + 20;
        patterns.CancelAt = patterns.Reads + 20;
        var token = clause ? headSource.Token : parameterSource.Token;
        var error = Assert.ThrowsAny<OperationCanceledException>(() => AlgorithmValidation.FindFirstPreEvaluationViolation(
            root, observations: null, graphIsAliasFree: true, cancellationToken: token));
        Assert.Equal(token, error.CancellationToken);
        Assert.InRange(clause ? head.Reads - head.ReadsAtCancel : patterns.Reads - patterns.ReadsAtCancel, 0, 2 * Block + 4);
    }

    private static long PreflightEdges(Expr program)
    {
        var observations = new FrontEndTraversalObservations();
        Assert.Null(AstStructuralPreflight.Check(program, Limit, Profile, observations));
        return observations.StructuralPreflightEdges;
    }

    [Fact]
    public void SourceElaborationPreflight_ObservesCancellationDuringTheWalk()
    {
        // The source gate shares this walk with the evaluator. Cancel on a list read so the entry
        // poll has already passed and a final check after a complete walk cannot satisfy the bound.
        var members = new CancellingList<Property>([.. SharedMembers(4 * Block)]);
        using var cancellation = members.Source;
        var root = new Algorithm.User(null, [], [], members, []);
        members.CancelAt = members.Reads + 10;

        var error = Assert.Throws<OperationCanceledException>(
            () => AstStructuralPreflight.CheckSourceElaboration(root, cancellation.Token));
        Assert.Equal(cancellation.Token, error.CancellationToken);
        Assert.Equal(members.CancelAt, members.ReadsAtCancel);
        Assert.InRange(members.Reads - members.ReadsAtCancel, 0, 2 * Block + 4);
    }

    [Fact]
    public void CancellationDuringAliasReachInOneWideBodyIsBounded()
    {
        var properties = new CancellingList<Property>([.. SharedMembers(8 * Block),
            new Property("A", new Algorithm.Alias(null, [], [], new Expr.Resolve("missing")))]);
        using var source = properties.Source;
        var root = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], properties, [new Expr.Num(1)]));
        properties.CancelAt = properties.Reads + 20;
        var error = Assert.ThrowsAny<OperationCanceledException>(() => AlgorithmValidation.FindFirstPreEvaluationViolation(
            root, observations: null, cancellationToken: source.Token));
        Assert.Equal(source.Token, error.CancellationToken);
        Assert.InRange(properties.Reads - properties.ReadsAtCancel, 0, 2 * Block + 4);
    }

    [Fact]
    public void CancelledColdSignatureCheckLeavesItsViolationForTheNextRun()
    {
        var nested = new CancellingList<ParameterPattern>([.. Enumerable.Repeat<ParameterPattern>(
            new CaptureParameterPattern("x"), 8 * Block), new SequenceValueParameterPattern([new CaptureParameterPattern("y")])]);
        using var source = nested.Source;
        var template = ImplicitSignatureTemplate.Flat([new ListValueParameterPattern(nested)]);
        nested.CancelAt = nested.Reads + 20;
        var work = new ValidationWork(null, source.Token);
        var error = Assert.ThrowsAny<OperationCanceledException>(() => ParameterPattern.FindSignatureViolation(template, work));
        Assert.Equal(source.Token, error.CancellationToken);
        Assert.InRange(nested.Reads - nested.ReadsAtCancel, 0, 2 * Block + 4);
        Assert.Equal(ParameterSignatureViolation.SingletonSequencePattern, ParameterPattern.FindSignatureViolation(template));
    }

    // ── The route-selection walk ────────────────────────────────────────────────────────────────────

    /// <summary>
    /// A cancellation requested inside the route walk stops it at the next block boundary: the walk followed exactly the
    /// blocks before the cancelling checkpoint, decided nothing, and no admission pass started — on the synchronous entry's
    /// guard, the async entry's fact for the fast path, and the async entry's fact for the twin path (a deferred root).
    /// The shared members are a DAG (every revisit is an edge); the rows are ONE node pushing all its children at once.
    /// </summary>
    [Theory]
    [InlineData("sync", "members", 2)]
    [InlineData("sync", "rows", 5)]
    [InlineData("sync", "deferred", 3)]
    [InlineData("async", "members", 3)]
    [InlineData("async", "rows", 2)]
    [InlineData("async", "deferred", 4)]
    public async Task TheRouteWalk_CancelledInside_StopsWithinOneBlockOfEdges(string route, string shape, long ordinal)
    {
        var program = shape == "deferred" ? HostDeferredRoot(8192).Root : Program(shape);
        Assert.InRange(RouteEdges(program), ordinal * Block, long.MaxValue);
        using var cancel = new CancelAt(FrontEndCancellationCheckpoint.EvaluatorRoute, ordinal);
        var observations = new EvaluationObservations { PreEvaluationTraversal = cancel.Observations };

        var error = route == "sync"
            ? Assert.ThrowsAny<OperationCanceledException>(() => Evaluator.RunCountedObserved(program,
                observations: observations, cancellationToken: cancel.Token))
            : await Assert.ThrowsAnyAsync<OperationCanceledException>(async () => await Evaluator.RunCountedObservedAsync(program,
                observations: observations, cancellationToken: cancel.Token));

        Assert.Equal(cancel.Token, error.CancellationToken);
        Assert.Equal((ordinal - 1) * Block, cancel.Observations.EvaluatorRouteEdges);
        Assert.Equal(ordinal, cancel.Observations.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.EvaluatorRoute));
        cancel.AssertNothingAfterTheCancellingCheckpoint();
        Assert.Equal(0, cancel.Observations.StructuralPreflightEdges);
        Assert.Equal(0, cancel.Observations.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.EvaluatorPreflight));
        Assert.Equal(0, cancel.Observations.WalkerSteps);
    }

    /// <summary>
    /// The public entries take no observer, so a host list counts the reads instead and cancels at the tenth: the walk
    /// reads at most one block of edges more (two reads per member edge) before the cancellation escapes, where it formerly
    /// read the rest of the list (131,066 reads for 65,536 members on main before this change). The deferred root is decided by the
    /// same walk on both families: the asynchronous entry routes it to the twin path, the synchronous one would reject it.
    /// </summary>
    [Theory]
    [InlineData("Run", false)]
    [InlineData("Run", true)]
    [InlineData("RunAsync", false)]
    [InlineData("RunAsync", true)]
    [InlineData("RunAsync(host operations)", false)]
    [InlineData("RunFlatAsync", false)]
    public async Task PublicEntries_StopTheirRouteWalk_WithinOneBlockOfReads(string entry, bool deferred)
    {
        CancellingList<Property>? members = null;
        IReadOnlyList<Property> Instrument(IReadOnlyList<Property> properties) => members = new CancellingList<Property>(properties);
        var program = deferred
            ? HostDeferredRoot(65_536, wrap: Instrument).Root
            : new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], Instrument([.. SharedMembers(65_536)]), [new Expr.Num(1)]));
        Assert.NotNull(members);
        members.CancelAt = 10;
        var token = members.Source.Token;

        Exception? thrown = entry switch
        {
            "Run" => Record.Exception(() => Evaluator.Run(program, limits: null, randomSeed: null, token)),
            "RunAsync" => await Record.ExceptionAsync(() => Evaluator.RunAsync(program, null, token)),
            "RunAsync(host operations)" => await Record.ExceptionAsync(() => Evaluator.RunAsync(program, SynchronousOperations(), null, null, token)),
            _ => await Record.ExceptionAsync(() => Evaluator.RunFlatAsync(program, null, token)),
        };

        var error = Assert.IsAssignableFrom<OperationCanceledException>(thrown);
        Assert.Equal(token, error.CancellationToken);
        Assert.Equal(10, members.ReadsAtCancel);
        Assert.InRange(members.Reads - members.ReadsAtCancel, 0, 2 * Block + 4);
        members.Source.Dispose();
    }

    /// <summary>
    /// A token that is never cancelled changes no route fact: the same answer, node count, hand-over and edges, with one
    /// checkpoint per block plus the start; a walk without a cancellable token records none.
    /// </summary>
    [Theory]
    [InlineData("members")]
    [InlineData("rows")]
    [InlineData("links")]
    [InlineData("deferred")]
    [InlineData("deferred-first")]
    public void ALiveToken_DecidesTheSameRouteFact(string shape)
    {
        var program = shape switch
        {
            "deferred" => HostDeferredRoot(8192).Root,
            "deferred-first" => HostDeferredRoot(8192, reachedLast: false).Root,
            _ => Program(shape),
        };
        using var live = new CancellationTokenSource();
        var plain = new FrontEndTraversalObservations();
        var plainTables = new PreEvaluationTables();
        var plainAnswer = DeferredModuleRegion.RequiresAsyncEvaluationCounting(program, out var plainCount, plainTables, plain);
        var observed = new FrontEndTraversalObservations();
        var liveTables = new PreEvaluationTables();
        var liveAnswer = DeferredModuleRegion.RequiresAsyncEvaluationCounting(program, out var liveCount, liveTables, observed, live.Token);

        Assert.Equal(plainAnswer, liveAnswer);
        Assert.Equal(shape.StartsWith("deferred", StringComparison.Ordinal), liveAnswer);
        Assert.Equal(plainCount, liveCount);
        Assert.Equal(plainTables.TakeNodeSet(0) is null, liveTables.TakeNodeSet(0) is null);
        Assert.Equal(plain.EvaluatorRouteEdges, observed.EvaluatorRouteEdges);
        Assert.Equal(0, plain.CancellationCheckpoints);
        Assert.Equal(1 + observed.EvaluatorRouteEdges / Block, observed.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.EvaluatorRoute));
        Assert.Equal(Evaluator.DecideTreeRequiresAsyncEvaluation(program, hostOperations: null),
            Evaluator.DecideTreeRequiresAsyncEvaluation(program, hostOperations: null, observations: null, live.Token));
    }

    /// <summary>
    /// Wrong configurations keep their precedence. The synchronous entry rejects asynchronous host operations before its
    /// route walk, so no checkpoint of that walk is reached even when one would cancel. It observes the token before every
    /// other pre-evaluation verdict, so a cancellation requested inside the walk, before it reaches a deferred placeholder,
    /// escapes as that cancellation, while a placeholder reached before the next block still rejects the tree.
    /// </summary>
    [Fact]
    public void TheSynchronousEntry_KeepsItsConfigurationPrecedence_AroundTheRouteWalk()
    {
        using (var cancel = new CancelAt(FrontEndCancellationCheckpoint.EvaluatorRoute, 1))
        {
            Assert.Throws<InvalidOperationException>(() => Evaluator.RunCountedObserved(Members(4096),
                observations: new EvaluationObservations { PreEvaluationTraversal = cancel.Observations },
                hostOperations: AsynchronousOperations(), cancellationToken: cancel.Token));
            Assert.Equal(0, cancel.Observations.CancellationCheckpoints);
            Assert.False(cancel.Token.IsCancellationRequested);
        }

        var lateRoot = HostDeferredRoot(8192).Root;
        using (var live = new CancellationTokenSource())
        {
            var rejected = Assert.Throws<InvalidOperationException>(() => Evaluator.RunCountedObserved(lateRoot,
                observations: new EvaluationObservations { PreEvaluationTraversal = new FrontEndTraversalObservations() },
                cancellationToken: live.Token));
            Assert.Equal(SynchronousDeferredRegionMessage, rejected.Message);
        }

        foreach (var ordinal in new long[] { 1, 3 })
        {
            using var cancel = new CancelAt(FrontEndCancellationCheckpoint.EvaluatorRoute, ordinal);
            var error = Assert.ThrowsAny<OperationCanceledException>(() => Evaluator.RunCountedObserved(lateRoot,
                observations: new EvaluationObservations { PreEvaluationTraversal = cancel.Observations }, cancellationToken: cancel.Token));
            Assert.Equal(cancel.Token, error.CancellationToken);
            cancel.AssertNothingAfterTheCancellingCheckpoint();
        }

        // The placeholder is reached at the walk's third edge: the walk rejects the tree before its second checkpoint.
        var earlyRoot = HostDeferredRoot(8192, reachedLast: false).Root;
        Assert.InRange(RouteEdges(earlyRoot), 1, Block - 1);
        using (var cancel = new CancelAt(FrontEndCancellationCheckpoint.EvaluatorRoute, 2))
        {
            var rejected = Assert.Throws<InvalidOperationException>(() => Evaluator.RunCountedObserved(earlyRoot,
                observations: new EvaluationObservations { PreEvaluationTraversal = cancel.Observations }, cancellationToken: cancel.Token));
            Assert.Equal(SynchronousDeferredRegionMessage, rejected.Message);
            Assert.Equal(1, cancel.Observations.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.EvaluatorRoute));
            Assert.False(cancel.Token.IsCancellationRequested);
        }
    }

    /// <summary>
    /// The one route walk that stays unobserved, and why: an internal caller pairing a deferred-region tree with a
    /// synchronous-only cache is a wiring bug the twin family reports even under a cancelled token, and only the route
    /// rule's complete walk can find the region that makes it one. A configuration with an asynchronous host operation
    /// routes before any walk, so no route checkpoint exists there either.
    /// </summary>
    [Fact]
    public async Task TheRouteRulesOwnWalk_KeepsTheCachePairingGuardAheadOfACancelledToken()
    {
        using var cancelled = new CancellationTokenSource();
        cancelled.Cancel();
        var root = HostDeferredRoot(8192).Root;
        var error = await Assert.ThrowsAsync<InvalidOperationException>(async () => await Evaluator.RunCountedAsync(
            root, new RunScopedZeroArgPropertyResultCache(), cancellationToken: cancelled.Token));
        Assert.Equal(DeferredRegionCachePairingMessage, error.Message);

        var observations = new FrontEndTraversalObservations();
        var thrown = await Assert.ThrowsAnyAsync<OperationCanceledException>(async () => await Evaluator.RunCountedObservedAsync(
            Members(4096), observations: new EvaluationObservations { PreEvaluationTraversal = observations },
            hostOperations: AsynchronousOperations(), cancellationToken: cancelled.Token));
        Assert.Equal(cancelled.Token, thrown.CancellationToken);
        Assert.Equal(0, observations.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.EvaluatorRoute));
        Assert.Equal(0, observations.EvaluatorRouteEdges);
    }

    // ── The validation walk inside one wide body ────────────────────────────────────────────────────

    /// <summary>
    /// The validation walk observes the token in blocks of work BELOW its algorithm expansions, so one wide body — its
    /// rows, one long comparison chain, a zero-weight spread chain, the prescans of a many-clause family, a wide parameter
    /// list (polled inside the scan) — stops within one block, after the complete preflight, on the synchronous route,
    /// the async fast path and the twin path. Formerly each of these bodies was one block of the walk.
    /// </summary>
    [Theory]
    [InlineData("sync", "rows", 2)]
    [InlineData("sync", "rows", 9)]
    [InlineData("async", "links", 3)]
    [InlineData("twin", "links", 4)]
    [InlineData("sync", "spread", 3)]
    [InlineData("twin", "spread", 5)]
    [InlineData("sync", "clauses", 3)]
    [InlineData("async", "clauses", 12)]
    [InlineData("sync", "parameters", 1)]
    [InlineData("twin", "parameters", 1)]
    public async Task TheValidationWalk_CancelledInsideOneWideBody_StopsWithinOneBlock(string route, string shape, long ordinal)
    {
        var program = Program(shape);
        var preflightEdges = PreflightEdges(program);
        using var cancel = new CancelAt(FrontEndCancellationCheckpoint.EvaluatorValidationBlock, ordinal);
        var observations = new EvaluationObservations { PreEvaluationTraversal = cancel.Observations };

        var error = route switch
        {
            "sync" => Assert.ThrowsAny<OperationCanceledException>(() => Evaluator.RunCountedObserved(program,
                observations: observations, cancellationToken: cancel.Token)),
            "async" => await Assert.ThrowsAnyAsync<OperationCanceledException>(async () => await Evaluator.RunCountedObservedAsync(program,
                observations: observations, cancellationToken: cancel.Token)),
            _ => await Assert.ThrowsAnyAsync<OperationCanceledException>(async () => await Evaluator.RunCountedObservedAsync(program,
                zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(),
                observations: observations, cancellationToken: cancel.Token)),
        };

        Assert.Equal(cancel.Token, error.CancellationToken);
        Assert.Equal(ordinal, cancel.Observations.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.EvaluatorValidationBlock));
        cancel.AssertNothingAfterTheCancellingCheckpoint();
        // The whole preflight ran first; the walk is inside ONE body (the root and at most one property's algorithm).
        Assert.Equal(preflightEdges, cancel.Observations.StructuralPreflightEdges);
        Assert.InRange(cancel.Observations.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.WalkerAlgorithm), 1, 2);
        Assert.InRange(cancel.Observations.WalkerExpressionExpansions, 0, ordinal * Block);
        if (shape == "parameters")
            // The first block falls inside structural signature validation, ahead of META placement.
            Assert.Equal(0, cancel.Observations.PreEvaluationMetaPlacementSlots);
    }

    /// <summary>
    /// A token that is never cancelled changes no validation verdict or walk: the same first violation, the same walker
    /// and META-placement counts and algorithm checkpoints; only the block checkpoints are added, none without a token.
    /// </summary>
    [Theory]
    [InlineData("rows")]
    [InlineData("links")]
    [InlineData("spread")]
    [InlineData("clauses")]
    [InlineData("parameters")]
    [InlineData("rows-violation")]
    [InlineData("clauses-mismatch")]
    public void ALiveToken_FindsTheSameFirstViolation_WithTheSameWalk(string shape)
    {
        var program = Program(shape);
        using var live = new CancellationTokenSource();
        var plain = new FrontEndTraversalObservations();
        var observed = new FrontEndTraversalObservations();
        var plainViolation = AlgorithmValidation.FindFirstPreEvaluationViolation(program, plain);
        var liveViolation = AlgorithmValidation.FindFirstPreEvaluationViolation(program, observed, cancellationToken: live.Token);

        Assert.Equal(plainViolation, liveViolation);
        Assert.Equal(shape switch
        {
            "rows-violation" => typeof(PreEvaluationAstViolation.ExplicitParametersWithoutOutput),
            "clauses-mismatch" => typeof(PreEvaluationAstViolation.ConditionalBranchArityMismatch),
            _ => null,
        }, liveViolation?.GetType());
        Assert.Equal(plain.WalkerSteps, observed.WalkerSteps);
        Assert.Equal(plain.WalkerAlgorithmExpansions, observed.WalkerAlgorithmExpansions);
        Assert.Equal(plain.PreEvaluationMetaPlacementSlots, observed.PreEvaluationMetaPlacementSlots);
        // The algorithm checkpoints are recorded with or without a token (one per expansion); the blocks only with one.
        Assert.Equal(plain.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.WalkerAlgorithm),
            observed.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.WalkerAlgorithm));
        Assert.Equal(0, plain.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.EvaluatorValidationBlock));
        // Each wide shape executes several blocks of actual traversal work.
        Assert.InRange(observed.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.EvaluatorValidationBlock),
            3, long.MaxValue);
    }

    // ── Deferred-body admission during evaluation ──────────────────────────────────────────────────

    private static string WideModule(int width)
        => "public X = 1\n" + string.Concat(Enumerable.Range(0, width).Select(i => $"public P{i} = {i % 10}\n"));

    // A dot chain weighs three evaluator units per link and one front-end unit: materialization admits it, the run refuses it.
    private static string DeepModule() => "public X = 1" + string.Concat(Enumerable.Repeat(".count", 120)) + "\n";

    /// <summary>
    /// A parsed family whose second clause loads <paramref name="module"/> on selection. A suspending download yields to
    /// the thread pool before it answers and counts each yield in <paramref name="downloadYields"/>.
    /// </summary>
    private static async Task<(Algorithm Root, DeferredModuleRegion Region)> DeferredFamily(
        string module, string output, bool suspendingDownload = false, StrongBox<int>? downloadYields = null)
    {
        var options = new RunOptions
        {
            AllowedHosts = ["katlang.org"],
            DownloadCode = suspendingDownload
                ? async (_, _) =>
                {
                    await Task.Yield();
                    if (downloadYields is not null)
                        Interlocked.Increment(ref downloadYields.Value);
                    return module;
                }
                : (_, _) => ValueTask.FromResult(module),
        };
        var root = (await SourceProvenance.ParseValidAsync($"One = 1\nF(0) = 42\nF(n) = {{ open '{Url}'\nX }}\n{output}", options)).Root;
        var regions = new List<DeferredModuleRegion>();
        var seen = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<object>([root]);
        while (pending.TryPop(out var node))
        {
            if (!seen.Add(node))
                continue;
            if (node is Algorithm { DeferredRegion: { } region } && !regions.Contains(region))
                regions.Add(region);
            for (var index = 0; AstStructuralPreflight.TryGetChild(node, index, out var child); index++)
                pending.Push(child);
        }

        return (root, Assert.Single(regions));
    }

    /// <summary>The innermost error of a failed result (context frames stripped), or <c>null</c> for a value.</summary>
    private static EvalError? Leaf(EvalResult<Evaluator.CountedResult> result)
    {
        if (!result.IsError)
            return null;
        var leaf = result.Error;
        while (leaf is EvalError.WithContext(_, var inner))
            leaf = inner;
        return leaf;
    }

    /// <summary>The twin path completing inline, or genuinely suspending at every property read.</summary>
    private static IZeroArgPropertyResultCache CacheFor(string path)
        => path == "suspended" ? new SuspendingAsyncZeroArgPropertyResultCache() : new PassThroughAsyncZeroArgPropertyResultCache();

    private static ValueTask<(EvalResult<Evaluator.CountedResult> Result, EvaluationBudget Budget)> RunDeferred(
        Algorithm root, IZeroArgPropertyResultCache cache, FrontEndTraversalObservations admission, CancellationToken cancellationToken)
        => Evaluator.RunCountedObservedAsync(
            new Expr.AlgorithmExpr(root),
            zeroArgPropertyResultCache: cache,
            observations: new EvaluationObservations { DeferredAdmissionTraversal = admission },
            cancellationToken: cancellationToken);

    /// <summary>
    /// A cancellation requested inside a deferred body's admission stops it within one block of edges — on the twin path
    /// completing inline, and on a genuinely suspended one — with the run's own token, carried to the entry point by value.
    /// On the suspended path the clause match reads <c>One</c> through a cache that yields to the thread pool
    /// (<see cref="Task.Yield"/>), and the module download yields too, both before the branch is selected, so the admission
    /// runs in a resumed run. Both yields are counted rather than inferred from task completion, which the pool may reach
    /// before the caller looks. The prefix accounting and the body check each start with a checkpoint, so the edges walked
    /// before the cancelling checkpoint never exceed one block per earlier checkpoint. The materialization belongs to the
    /// region and stays.
    /// </summary>
    [Theory]
    [InlineData("inline", 2)]
    [InlineData("inline", 6)]
    [InlineData("suspended", 2)]
    [InlineData("suspended", 5)]
    public async Task ADeferredBodyAdmission_CancelledInside_StopsWithinOneBlockOfEdges(string path, long ordinal)
    {
        var downloadYields = new StrongBox<int>();
        var (root, region) = await DeferredFamily(
            WideModule(4096), path == "suspended" ? "F(One)" : "F(1)", path == "suspended", downloadYields);
        using var cancel = new CancelAt(FrontEndCancellationCheckpoint.EvaluatorDeferredAdmission, ordinal);
        var cache = CacheFor(path);

        var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(async () =>
            await RunDeferred(root, cache, cancel.Observations, cancel.Token));

        if (cache is SuspendingAsyncZeroArgPropertyResultCache suspending)
        {
            Assert.InRange(suspending.AsyncAccesses, 1, int.MaxValue);
            Assert.Equal(1, downloadYields.Value);
        }

        Assert.Equal(cancel.Token, error.CancellationToken);
        Assert.Equal(ordinal, cancel.Observations.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.EvaluatorDeferredAdmission));
        cancel.AssertNothingAfterTheCancellingCheckpoint();
        Assert.InRange(cancel.Observations.StructuralPreflightEdges + cancel.Observations.DeferredRegionPrefixEdges,
            0, (ordinal - 1) * Block);
        Assert.True(region.IsMaterialized);
        Assert.Equal(1, region.MaterializationAttempts);
    }

    /// <summary>
    /// A token that is never cancelled changes no admission: the same value or rejection, the same body and prefix edges,
    /// and a repeated selection of an admitted body observes nothing (the checkpoints are the two passes' starts and their
    /// blocks). An admission without a cancellable token records no checkpoint.
    /// </summary>
    [Theory]
    [InlineData("inline", false)]
    [InlineData("suspended", false)]
    [InlineData("inline", true)]
    public async Task ALiveToken_AdmitsTheSameBodies_AndARepeatedSelectionObservesNothing(string path, bool deep)
    {
        var call = path == "suspended" ? "F(One)" : "F(1)";
        var (root, _) = await DeferredFamily(deep ? DeepModule() : WideModule(4096), $"{call} + {call}", path == "suspended");
        var plain = new FrontEndTraversalObservations();
        var (plainResult, _) = await RunDeferred(root, CacheFor(path), plain, default);
        using var live = new CancellationTokenSource();
        var observed = new FrontEndTraversalObservations();
        var (liveResult, _) = await RunDeferred(root, CacheFor(path), observed, live.Token);

        Assert.Equal(AsyncEvaluationHarness.NeutralOf(plainResult), AsyncEvaluationHarness.NeutralOf(liveResult));
        Assert.Equal(plainResult.IsError ? plainResult.Error.Span : null, liveResult.IsError ? liveResult.Error.Span : null);
        Assert.Equal(deep, Leaf(liveResult) is EvalError.AstDepthLimitExceeded);
        if (!deep)
            Assert.Equal([(Decimal128)2], liveResult.Value.Value.ToAtoms());
        Assert.Equal(plain.StructuralPreflightEdges, observed.StructuralPreflightEdges);
        Assert.Equal(plain.DeferredRegionPrefixEdges, observed.DeferredRegionPrefixEdges);
        Assert.Equal(0, plain.CancellationCheckpoints);
        var checkpoints = observed.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.EvaluatorDeferredAdmission);
        if (deep)
            // The prefix accounting, the check and the replay that positions the rejection each start with one.
            Assert.InRange(checkpoints, 3, long.MaxValue);
        else
            Assert.Equal(2 + observed.DeferredRegionPrefixEdges / Block + observed.StructuralPreflightEdges / Block, checkpoints);
    }

    /// <summary>
    /// A run cancelled inside its admission leaves nothing a later run can reuse: the next run admits the cached
    /// materialization in full — exactly the walk of a run that was never cancelled — and evaluates it, and a body the
    /// cancelled run never finished judging is still refused by the next run.
    /// </summary>
    [Theory]
    [InlineData(false, 5)]
    [InlineData(true, 2)]
    [InlineData(true, 3)]
    public async Task ARunCancelledInsideItsAdmission_LeavesTheNextRunToAdmitTheBodyInFull(bool deep, long ordinal)
    {
        var (root, region) = await DeferredFamily(deep ? DeepModule() : WideModule(4096), "F(1)");
        using (var cancel = new CancelAt(FrontEndCancellationCheckpoint.EvaluatorDeferredAdmission, ordinal))
        {
            var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(async () =>
                await RunDeferred(root, CacheFor("inline"), cancel.Observations, cancel.Token));
            Assert.Equal(cancel.Token, error.CancellationToken);
        }

        using var live = new CancellationTokenSource();
        var next = new FrontEndTraversalObservations();
        var (nextResult, _) = await RunDeferred(root, CacheFor("inline"), next, live.Token);
        var control = new FrontEndTraversalObservations();
        var (controlResult, _) = await RunDeferred(root, CacheFor("inline"), control, default);

        if (deep)
            Assert.IsType<EvalError.AstDepthLimitExceeded>(Leaf(nextResult));
        else
            Assert.Equal([(Decimal128)1], nextResult.Value.Value.ToAtoms());
        Assert.Equal(AsyncEvaluationHarness.NeutralOf(controlResult), AsyncEvaluationHarness.NeutralOf(nextResult));
        Assert.Equal(control.StructuralPreflightEdges, next.StructuralPreflightEdges);
        Assert.Equal(control.DeferredRegionPrefixEdges, next.DeferredRegionPrefixEdges);
        Assert.Equal(1, region.MaterializationAttempts);
    }

    /// <summary>
    /// A host-built admission with a nested region in its body: a cancellation in any of its passes — the prefix walk over
    /// the root, the body check, the prefix walk over the admitted body — ABANDONS the admission. Its partial prefixes and
    /// arrivals are never read again: every later call rethrows the run's cancellation without walking (the nested region
    /// registered by the interrupted walk would otherwise be unknown, or known at a partial prefix), while a fresh
    /// admission decides exactly what a never-cancelled one decides.
    /// </summary>
    [Theory]
    [InlineData("root-prefix")]
    [InlineData("body-check")]
    [InlineData("body-prefix")]
    public void ACancelledAdmission_IsAbandoned_AndNeverReusesItsPartialState(string pass)
    {
        var raw = new Algorithm.User(null, [], [], [], [new Expr.Num(1)]);
        var loader = new ModuleLoader(new DiagnosticBag(), (_, _) => ValueTask.FromResult("public X = 1"));
        var outer = new DeferredModuleRegion(loader, raw, ModuleLoader.LoadContext.PropertyDef, 0, 0, null, []);
        var nested = new DeferredModuleRegion(loader, raw, ModuleLoader.LoadContext.PropertyDef, 0, 0, null, []);
        var root = new Expr.AlgorithmExpr(raw with
        {
            Properties = [new Property("F", raw with { DeferredRegion = outer }), .. SharedMembers(2048)],
        });
        var body = raw with { Properties = [new Property("G", raw with { DeferredRegion = nested }), .. SharedMembers(2048, "Q")] };
        var nestedBody = raw with { Properties = [.. SharedMembers(16, "R")] };

        // The never-cancelled reference, logging each checkpoint's position in the passes.
        var log = new List<(long Ordinal, long Prefix, long Body)>();
        FrontEndTraversalObservations? reference = null;
        reference = new FrontEndTraversalObservations
        {
            CheckpointReached = (_, ordinal) => log.Add((ordinal, reference!.DeferredRegionPrefixEdges, reference!.StructuralPreflightEdges)),
        };
        using var live = new CancellationTokenSource();
        var control = new DeferredBodyAdmission(root, Limit, reference, live.Token);
        Assert.Null(control.Admit(outer, body));
        Assert.Null(control.Admit(nested, nestedBody));
        var rootPrefixEdges = log.First(entry => entry.Body > 0).Prefix;
        var ordinal = pass switch
        {
            "root-prefix" => log.First(entry => entry.Prefix > 0).Ordinal,
            "body-check" => log.First(entry => entry.Body > 0).Ordinal,
            _ => log.First(entry => entry.Prefix > rootPrefixEdges).Ordinal,
        };

        using var cancel = new CancelAt(FrontEndCancellationCheckpoint.EvaluatorDeferredAdmission, ordinal);
        var admission = new DeferredBodyAdmission(root, Limit, cancel.Observations, cancel.Token);
        var first = Assert.ThrowsAny<OperationCanceledException>(() => admission.Admit(outer, body));
        Assert.Equal(cancel.Token, first.CancellationToken);
        cancel.AssertNothingAfterTheCancellingCheckpoint();

        // Abandoned: no later call walks or reads the partial state, whichever region it names.
        var again = Assert.ThrowsAny<OperationCanceledException>(() => admission.Admit(outer, body));
        Assert.Equal(cancel.Token, again.CancellationToken);
        var inner = Assert.ThrowsAny<OperationCanceledException>(() => admission.Admit(nested, nestedBody));
        Assert.Equal(cancel.Token, inner.CancellationToken);
        cancel.AssertNothingAfterTheCancellingCheckpoint();

        // A fresh admission of the same run shape decides what the reference decided, walk for walk.
        var fresh = new FrontEndTraversalObservations();
        using var other = new CancellationTokenSource();
        var retry = new DeferredBodyAdmission(root, Limit, fresh, other.Token);
        Assert.Null(retry.Admit(outer, body));
        Assert.Null(retry.Admit(nested, nestedBody));
        Assert.Equal(reference.DeferredRegionPrefixEdges, fresh.DeferredRegionPrefixEdges);
        Assert.Equal(reference.StructuralPreflightEdges, fresh.StructuralPreflightEdges);
        // An admitted body is one lookup from then on.
        Assert.Null(retry.Admit(nested, nestedBody));
        Assert.Equal(reference.StructuralPreflightEdges, fresh.StructuralPreflightEdges);
    }

    /// <summary>
    /// An admission's cancellation is the run's ordinary cancellation: thrown with the run's token outside an asynchronous
    /// twin run's boundary, and inside it retained once while the run's marker comes back, rethrown by the entry point.
    /// It is never a structural verdict, and the abandoned admission stays cancelled.
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void AnAdmissionCancellation_IsThrownOrCarried_AsTheRunsCancellation(bool carried)
    {
        var (root, region) = HostDeferredRoot(4096);
        var body = new Algorithm.User(null, [], [], [.. SharedMembers(4096, "Q")], [new Expr.Num(1)]);
        using var cancel = new CancelAt(FrontEndCancellationCheckpoint.EvaluatorDeferredAdmission, 3);
        var budget = EvaluationBudget.Create(null, cancellationToken: cancel.Token);
        budget.RecordDeferredBodyAdmission(root, Limit, cancel.Observations);

        OperationCanceledException error;
        if (carried)
        {
            budget.OpenHostTerminationBoundary();
            var marker = budget.AdmitDeferredBody(region, body);
            Assert.NotNull(marker);
            Assert.True(marker.IsHostTermination);
            Assert.True(budget.CheckContinuation()?.IsHostTermination);
            budget.CloseHostTerminationBoundary();
            error = Assert.ThrowsAny<OperationCanceledException>(budget.RethrowHostTermination);
        }
        else
        {
            error = Assert.ThrowsAny<OperationCanceledException>(() => budget.AdmitDeferredBody(region, body));
            Assert.ThrowsAny<OperationCanceledException>(() => budget.AdmitDeferredBody(region, body));
        }

        Assert.Equal(cancel.Token, error.CancellationToken);
        Assert.Equal(3, cancel.Observations.CancellationCheckpointsOf(FrontEndCancellationCheckpoint.EvaluatorDeferredAdmission));
        cancel.AssertNothingAfterTheCancellingCheckpoint();
    }
}
