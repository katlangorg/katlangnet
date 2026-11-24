using System.Numerics;
using System.Reflection;
using System.Text;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using static KatLang.Tests.RootPropertyObservations.PropertyObservationTestSupport;

namespace KatLang.Tests.RootPropertyObservations;

/// <summary>
/// A LIST READ ONE POSITION AT A TIME IS OBSERVED FROM ITS COMPLETED POSITIONS (lazy collections,
/// issue #204; C#-only host policy). A list evaluated on demand can have every position read —
/// selected one at a time in any order, or judged by a <c>filter</c>'s verdicts — without a
/// consumer ever building its whole or one-level form. When the run has SETTLED the list's
/// cardinality and the VALUE of every position has completed successfully, the passive snapshot
/// assembles the observed value from those memoized values and the property is
/// <see cref="PropertyValueStatus.Available"/>; a cardinality the run did not settle, a position it
/// did not read or that failed, a nested list read too little, a cycle or a call reference still
/// withholds it (<c>Evaluator.TrySnapshotValue</c>, <c>Evaluator.TryReadCompletedPositions</c>).
/// <para>Taking the snapshot reads only completed data: it never demands a cell, discovers a
/// candidate, reserves, charges, performs an effect or observes cancellation. Every program runs on
/// the synchronous, asynchronous and genuinely suspending engine routes with observation off and on;
/// the outcome and the host-call log must not change, and the log must be exactly what the program
/// itself reads.</para>
/// </summary>
public class PropertyObservationPositionReadTests
{
    private static readonly string[] Engines = ["sync", "async", "suspending"];

    private static Task<RunResult> RunOn(string engine, string source, RunOptions options)
        => engine == "sync" ? Task.FromResult(KatLangEngine.Run(source, options)) : KatLangEngine.RunAsync(source, options);

    /// <summary>
    /// Runs <paramref name="source"/> on every engine route with observation off and on: the outcome
    /// and the host-call log are the same either way, the log is <paramref name="expectedLog"/>, and
    /// the snapshot is <paramref name="expectedObservations"/> on every route.
    /// </summary>
    private static async Task<RunResult[]> ObserveOnEveryEngine(string source, string expectedObservations, string expectedLog)
    {
        var observed = new List<RunResult>();
        foreach (var engine in Engines)
        {
            var offLog = new TickLog();
            var onLog = new TickLog();
            AssertLegal(source, offLog.Operations());
            var off = await RunOn(engine, source, Options(observe: false, offLog.Operations(engine == "suspending")));
            var on = await RunOn(engine, source, Options(observe: true, onLog.Operations(engine == "suspending")));

            Assert.Equal(Outcome(off), Outcome(on));
            Assert.Equal(offLog.Calls, onLog.Calls);
            Assert.Equal(expectedLog, string.Join(",", onLog.Calls));
            Assert.Null(off.PropertyObservations);
            Assert.Equal(expectedObservations, Describe(on));
            observed.Add(on);
        }

        Assert.All(observed, result => Assert.Equal(Outcome(observed[0]), Outcome(result)));
        return [.. observed];
    }

    private static string Display(RunResult result)
        => Assert.IsType<RunResult.Success>(result).ToDisplayString().ReplaceLineEndings("\n");

    // ── 1. Every position read, one at a time: available ──────────────────────────────────────

    /// <summary>source, expected output, expected snapshot, expected host-call log.</summary>
    public static TheoryData<string, string, string, string> ReadEveryPosition() => new()
    {
        // Selected one at a time out of source order, then read again (each position's one VALUE).
        { "L = [tock(), tock(), tock()]\nL[2]\nL[0]\nL[1]\nL[2] + L[0] + L[1]", "0\n1\n2\n3", "L=[1, 2, 0]#1", "tock:0,tock:1,tock:2" },
        // Several selectors at once, in their written order; position 2 is read twice.
        { "L = [tock(), tock(), tock()]\nL[2, 0]\nL[1, 2]", "(0, 1)\n(2, 0)", "L=[1, 2, 0]#1", "tock:0,tock:1,tock:2" },
        // A `map` stage of known cardinality: each position's mapper ran when it was read.
        { "M = [10, 20, 30].map{trace(x)}\nM[1]\nM[2]\nM[0]", "20\n30\n10", "M=[10, 20, 30]#1", "trace:20,trace:30,trace:10" },
        // A `take` prefix: its positions are its source's first two.
        { "P = [tock(), tock(), tock()].take(2)\nP[1]\nP[0]", "0\n1", "P=[1, 0]#1", "tock:0,tock:1" },
        // A completed scan: every verdict read its candidate, so every accepted position is read.
        { "F = [tock(), tock(), tock()].filter{x >= 1}\nF.count", "2", "F=[1, 2]#1", "tock:0,tock:1,tock:2" },
        { "F = [tock(), tock(), tock()].filter{x >= 1}\nF.last", "2", "F=[1, 2]#1", "tock:0,tock:1,tock:2" },
        // A scan whose positions were read and then completed by a later consumer.
        { "F = [tock(), tock(), tock()].filter{x >= 1}\nF[1]\nF.count", "2\n2", "F=[1, 2]#1", "tock:0,tock:1,tock:2" },
        // Known to be empty: a completed scan that accepted nothing, and the stages over it.
        { "E = [tock(), tock()].filter{x > 5}\nE.count", "0", "E=[]#1", "tock:0,tock:1" },
        { "E = [tock(), tock()].filter{x > 5}.map{x * 2}\nE.count", "0", "E=[]#1", "tock:0,tock:1" },
        { "E = [tock()].filter{x > 5}.take(3)\nE.count", "0", "E=[]#1", "tock:0" },
    };

    [Theory]
    [MemberData(nameof(ReadEveryPosition))]
    public async Task AListWhosePositionsWereAllRead_IsAvailable(string source, string expectedDisplay, string expectedObservations, string expectedLog)
    {
        foreach (var result in await ObserveOnEveryEngine(source, expectedObservations, expectedLog))
        {
            Assert.Equal(expectedDisplay, Display(result));
            var observation = Assert.Single(result.PropertyObservations!);
            Assert.Equal(PropertyValueStatus.Available, observation.Status);
            Assert.Equal(1, observation.EmittedCount);
            Assert.Equal(new SourceSpan(1, 1, 1, 2), observation.DeclarationSpan);
            Assert.False(Evaluator.ContainsLazyList(observation.Value!));
        }
    }

    // ── 2. Read too little: withheld, and nothing more is read for the observer ───────────────

    /// <summary>source, expected output, expected snapshot, expected host-call log.</summary>
    public static TheoryData<string, string, string, string> ReadTooLittle() => new()
    {
        // Sparse reads: position 1 was never read, and the observer does not read it either.
        { "L = [tock(), tock(), tock()]\nL[2]\nL[0]", "0\n1", "L=<withheld>#1", "tock:0,tock:1" },
        { "M = [10, 20, 30].map{trace(x)}\nM[1]", "20", "M=<withheld>#1", "trace:20" },
        // Counted only: the cardinality is known, no position was read.
        { "L = [tock(), tock()]\nL.count", "2", "L=<withheld>#1", "" },
        { "M = [tock(), tock()].filter{x >= 0}.map{x + 1}\nM.count", "2", "M=<withheld>#1", "tock:0,tock:1" },
        // An unsettled scan: it found its first match and was asked for nothing more.
        { "F = [tock(), tock(), tock()].filter{x >= 1}\nF.first", "1", "F=<withheld>#1", "tock:0,tock:1" },
        // Still unsettled when every candidate has been judged: no reader asked past the last match,
        // so the scan never completed, and the observer does not complete it.
        { "F = [tock(), tock(), tock()].filter{x >= 1}\nF[1]", "2", "F=<withheld>#1", "tock:0,tock:1,tock:2" },
        // Every outer position read, but the nested list only at one of its positions.
        { "Outer = [[tock(), tock()]]\nOuter[0][1]", "0", "Outer=<withheld>#1", "tock:0" },
        // A list that holds itself through a read position: a cycle, never an unbounded snapshot.
        { "L = [L, tock()]\nL[1] + count(L[0])", "2", "L=<withheld>#1", "tock:0" },
        { "A = [B]\nB = [A]\ncount(A[0]) + count(B[0])", "2", "A=<withheld>#1; B=<withheld>#1", "" },
        // Every position read, one of them a call reference: the run-result boundary withholds it.
        {
            "Square(x) = x * x\nCapture(meta operation) = operation\nR = Capture(Square(5))\nL = [R, tock()]\nL[1]\nL[0] == L[0]",
            "0\ntrue", "L=<withheld>#1; R=<withheld>#1", "tock:0"
        },
    };

    [Theory]
    [MemberData(nameof(ReadTooLittle))]
    public async Task AListReadTooLittle_IsWithheld_AndTheObserverReadsNothingMore(string source, string expectedDisplay, string expectedObservations, string expectedLog)
    {
        foreach (var result in await ObserveOnEveryEngine(source, expectedObservations, expectedLog))
        {
            Assert.Equal(expectedDisplay, Display(result));
            foreach (var observation in result.PropertyObservations!)
            {
                Assert.Equal(PropertyValueStatus.Withheld, observation.Status);
                Assert.Null(observation.Value);
                Assert.Equal(1, observation.EmittedCount);
            }
        }
    }

    /// <summary>
    /// A position whose read FAILED ends the run, and the snapshot of what was published before the
    /// failure withholds the list: a failed position is not a value.
    /// </summary>
    [Fact]
    public async Task APositionWhoseReadFailed_IsNotAValue()
    {
        foreach (var result in await ObserveOnEveryEngine("L = [tock(), 1 / 0]\nL[0]\nL[1]", "L=<withheld>#1", "tock:0"))
        {
            var failure = Assert.IsType<RunResult.EvalFailure>(result);
            Assert.Equal(KatLangErrorCode.DivisionByZero, Assert.Single(failure.Errors).Code);
        }
    }

    // ── 3. Nesting and sharing ────────────────────────────────────────────────────────────────

    /// <summary>
    /// Lists nested in read positions are assembled the same way, and a list reached twice is
    /// assembled once: both positions of <c>Outer</c> that hold <c>Inner</c>, and <c>Inner</c>'s own
    /// observation, are one shared value. A position's concrete value is shared as it is.
    /// </summary>
    [Fact]
    public async Task NestedAndSharedLists_AreAssembledOnce_AndStayShared()
    {
        const string source = "Inner = [tock(), tock()]\nOuter = [Inner, [tock()], Inner]\nOuter[2][1]\nOuter[1][0]\nOuter[0][0]";
        foreach (var result in await ObserveOnEveryEngine(source, "Outer=[[2, 0], [1], [2, 0]]#1; Inner=[2, 0]#1", "tock:0,tock:1,tock:2"))
        {
            Assert.Equal("0\n1\n2", Display(result));
            var outer = Assert.IsType<Result.ListValue>(Single(result, "Outer").Value).Items;
            Assert.Same(outer[0], outer[2]);
            Assert.Same(Single(result, "Inner").Value, outer[0]);
        }

        const string concrete = "Big = range(1, 50)\nL = [Big, tock()]\nL[1]\ncount(L[0])";
        var big = "[" + string.Join(", ", Enumerable.Range(1, 50)) + "]";
        foreach (var result in await ObserveOnEveryEngine(concrete, $"L=[{big}, 0]#1; Big={big}#1", "tock:0"))
        {
            Assert.Equal("0\n50", Display(result));
            var positions = Assert.IsType<Result.ListValue>(Single(result, "L").Value).Items;
            Assert.Same(Single(result, "Big").Value, positions[0]);
        }
    }

    /// <summary>
    /// A one-level form and read positions compose: <c>Outer</c>'s level was built by <c>skip</c>,
    /// <c>Inner</c> was only ever read one position at a time.
    /// </summary>
    [Fact]
    public async Task AOneLevelFormHoldingAListReadOnePositionAtATime_IsAvailable()
    {
        const string source = "Inner = [tock(), tock()]\nOuter = [Inner, 5 + 5]\nOuter.skip(2)\nInner[1]\nInner[0]";
        foreach (var result in await ObserveOnEveryEngine(source, "Outer=[[1, 0], 10]#1; Inner=[1, 0]#1", "tock:0,tock:1"))
        {
            Assert.Equal("[]\n0\n1", Display(result));
            var outer = Assert.IsType<Result.ListValue>(Single(result, "Outer").Value).Items;
            Assert.Same(Single(result, "Inner").Value, outer[0]);
        }
    }

    /// <summary>
    /// A shared list read too little withholds every observation that reaches it; once the run
    /// has read it, each of them is available and they share its snapshot.
    /// </summary>
    [Fact]
    public async Task ASharedListReadTooLittle_WithholdsEveryValueThatHoldsIt_UntilItIsRead()
    {
        const string partial = "Shared = [tock(), tock()]\nA = [Shared, 1 + 1]\nB = [Shared, 2 + 2]\nA[1] + B[1] + count(A[0]) + count(B[0]) + Shared[0]";
        foreach (var result in await ObserveOnEveryEngine(partial, "A=<withheld>#1; B=<withheld>#1; Shared=<withheld>#1", "tock:0"))
            Assert.Equal("10", Display(result));

        const string complete = partial + " + Shared[1]";
        foreach (var result in await ObserveOnEveryEngine(complete, "A=[[0, 1], 2]#1; B=[[0, 1], 4]#1; Shared=[0, 1]#1", "tock:0,tock:1"))
        {
            Assert.Equal("11", Display(result));
            var shared = Single(result, "Shared").Value;
            Assert.Same(shared, Assert.IsType<Result.ListValue>(Single(result, "A").Value).Items[0]);
            Assert.Same(shared, Assert.IsType<Result.ListValue>(Single(result, "B").Value).Items[0]);
        }
    }

    // ── 4. The snapshot itself evaluates nothing ──────────────────────────────────────────────

    // The positions of one published list as the run left them, read passively: the cardinality
    // found and settled, and per found position whether it is a value, has no cell, or holds a cell
    // that is unread, done (a successful VALUE) or otherwise ended.
    private static string PositionState(Evaluator.LazyList list)
    {
        var text = new StringBuilder($"found={list.Discovered} settled={list.SettledCount}:");
        for (var index = 0; index < list.Discovered; index++)
        {
            text.Append(' ').Append(list.PeekSlot(index) switch
            {
                null => "none",
                Result => "value",
                NeedCell cell when cell.TryGetCompletedValue(out _) => "done",
                NeedCell cell when cell.IsValueUnstarted => "unread",
                NeedCell cell when cell.HasCompletedValue => "failed",
                _ => "other",
            });
        }

        return text.ToString();
    }

    private static string BudgetState(EvaluationBudget budget)
        => $"steps={budget.ConsumedSteps} checkpoints={budget.ConsumedExpressionCheckpoints} items={budget.MaterializedItems}"
            + $" chars={budget.MaterializedStringChars} transient={budget.PeakTransientExpansion}"
            + $" structural={budget.ConsumedStructuralWorkUnits} ticks={budget.TickCount}";

    private static Dictionary<string, Evaluator.LazyList> PublishedLists(RootPropertyObservationSink sink)
    {
        var records = (System.Collections.IEnumerable)typeof(RootPropertyObservationSink)
            .GetField("_records", BindingFlags.Instance | BindingFlags.NonPublic)!
            .GetValue(sink)!;
        var lists = new Dictionary<string, Evaluator.LazyList>();
        foreach (var record in records)
        {
            var (binding, published) = ((Property, ZeroArgPropertyResult))record;
            lists.Add(binding.Name, Assert.IsType<Result.ListValue>(published.Value).Lazy!);
        }

        return lists;
    }

    /// <summary>
    /// The evaluator-level proof of passivity, on the synchronous and the forced asynchronous route:
    /// taking the snapshot changes no budget counter, demands no cell (an unread position stays
    /// unstarted), creates no position cell, discovers and completes no scan, calls no host
    /// operation, and does not observe the run's token — cancelled after the run, it would make an
    /// ordinary demand throw, while the snapshot still shows the list read whole by positions.
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task TakingTheSnapshot_EvaluatesNothing_AndLeavesTheRunAsItEnded(bool asynchronous)
    {
        const string source = """
            Sparse = [tock(), tock(), tock()]
            Mapped = [10, 20, 30].map{trace(x)}
            Scan = [tock(), tock(), tock()].filter{x >= 0}
            Whole = [tock(), tock()]
            Sparse[2] + Mapped[1] + Scan[1] + Whole[1] + Whole[0]
            """;
        var log = new TickLog();
        var operations = log.Operations();
        var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        var sink = new RootPropertyObservationSink(parsed.Root);
        var program = new Expr.AlgorithmExpr(parsed.Root);
        using var cancellation = new CancellationTokenSource();

        var (result, budget) = asynchronous
            ? await Evaluator.RunCountedObservedAsync(
                program,
                zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(sink),
                hostOperations: operations,
                cancellationToken: cancellation.Token)
            : Evaluator.RunCountedObserved(
                program,
                zeroArgPropertyResultCache: new RunScopedZeroArgPropertyResultCache(sink),
                hostOperations: operations,
                cancellationToken: cancellation.Token);
        Assert.False(result.IsError, result.ToString());
        Assert.Equal("29", SemanticExplorerHarness.Neutral(result.Value.Value));
        Assert.Equal(["tock:0", "trace:20", "tock:1", "tock:2", "tock:3", "tock:4"], log.Calls);

        var lists = PublishedLists(sink);
        var before = lists.ToDictionary(static entry => entry.Key, static entry => PositionState(entry.Value));
        Assert.Equal("found=3 settled=3: unread unread done", before["Sparse"]);
        Assert.Equal("found=3 settled=3: none done none", before["Mapped"]);
        Assert.Equal("found=2 settled=-1: done done", before["Scan"]);
        Assert.Equal("found=2 settled=2: done done", before["Whole"]);
        var budgetBefore = BudgetState(budget);

        cancellation.Cancel();
        var snapshot = sink.Complete();

        Assert.Equal(
            "Sparse=Withheld; Mapped=Withheld; Scan=Withheld; Whole=Available",
            string.Join("; ", snapshot.Select(static o => $"{o.Name}={o.Status}")));
        var whole = Assert.Single(snapshot, static o => o.Name == "Whole");
        Assert.Equal("L[4, 3]", SemanticExplorerHarness.Neutral(whole.Value!));
        Assert.Equal(budgetBefore, BudgetState(budget));
        Assert.Equal(6, log.Calls.Count);
        foreach (var (name, list) in lists)
            Assert.Equal(before[name], PositionState(list));

        // The token the snapshot ignored is one an ordinary demand observes.
        var read = Assert.IsType<NeedCell>(lists["Whole"].PeekSlot(0));
        Assert.ThrowsAny<OperationCanceledException>(() => read.Demand());
    }

    /// <summary>
    /// The snapshot work is bounded by what the run read: a settled list of 50,000 positions read
    /// at its first one is withheld after inspecting the positions up to the first it lacks, and
    /// allocates nothing in proportion to its cardinality (a full array of its positions would be
    /// 400 KB; the bound leaves room for the snapshot's own small structures and the ~8 KB
    /// allocation-counter quantum).
    /// </summary>
    [Fact]
    public void AWideListReadAtOnePosition_IsWithheldWithoutWorkInProportionToItsCardinality()
    {
        const string source = "M = range(1, 50000).map{x + 1}\nM[0]";
        static RootPropertyObservationSink RunObserved()
        {
            var parsed = Parser.Parse(source);
            Assert.False(parsed.HasErrors);
            var sink = new RootPropertyObservationSink(parsed.Root);
            var (result, _) = Evaluator.RunCountedObserved(
                new Expr.AlgorithmExpr(parsed.Root),
                zeroArgPropertyResultCache: new RunScopedZeroArgPropertyResultCache(sink));
            Assert.False(result.IsError, result.ToString());
            return sink;
        }

        _ = RunObserved().Complete();
        var sink = RunObserved();
        var list = PublishedLists(sink)["M"];
        Assert.Equal(50000, list.SettledCount);
        Assert.IsType<NeedCell>(list.PeekSlot(0));
        Assert.Null(list.PeekSlot(1));

        var allocatedBefore = GC.GetAllocatedBytesForCurrentThread();
        var snapshot = sink.Complete();
        var allocated = GC.GetAllocatedBytesForCurrentThread() - allocatedBefore;

        Assert.Equal(PropertyValueStatus.Withheld, Assert.Single(snapshot).Status);
        Assert.True(allocated < 64 * 1024, $"the snapshot allocated {allocated} bytes");
    }

    [Fact]
    public void RootsSharingADeepConcreteValue_DoNotRescanItForLazyLists()
    {
        Result graph = new Result.Atom(1);
        for (var depth = 0; depth < 2048; depth++)
            graph = new Result.ListValue([graph]);

        Dictionary<Result, Result?>? snapshots = null;
        Assert.True(Evaluator.TrySnapshotValue(graph, ref snapshots, out var concrete));
        Assert.Same(graph, concrete);

        // Each additional root has one edge into the already inspected graph. Repeating a
        // separate lazy-list scan would allocate a depth-2048 traversal stack for every root.
        var roots = Enumerable.Range(0, 32).Select(_ => new Result.SequenceValue([graph])).ToArray();
        var before = GC.GetAllocatedBytesForCurrentThread();
        foreach (var root in roots)
        {
            Assert.True(Evaluator.TrySnapshotValue(root, ref snapshots, out var observed));
            Assert.Same(root, observed);
        }
        var allocated = GC.GetAllocatedBytesForCurrentThread() - before;
        Assert.True(allocated < 128 * 1024, $"additional roots allocated {allocated} bytes");
    }

    /// <summary>
    /// The cell inspection the snapshot uses reads the VALUE memo and nothing else: unstarted, in
    /// flight, failed and thrown cells have no completed value; a Ready cell and a completed success
    /// have one; a refused transport has none; and a completed success is read even after the cell's
    /// token was cancelled, where a demand throws.
    /// </summary>
    [Fact]
    public void TheCellInspection_ReadsOnlyACompletedSuccess_AndObservesNothing()
    {
        static EvalResult<Evaluator.CountedResult> Value(int number)
            => EvalResult<Evaluator.CountedResult>.Ok(new(new Result.Atom((Decimal128)number), 1));

        bool? whileInFlight = null;
        NeedCell? running = null;
        running = new NeedCell(
            () =>
            {
                whileInFlight = running!.TryGetCompletedValue(out _);
                return Value(7);
            },
            () => new(Value(7)));
        Assert.False(running.TryGetCompletedValue(out _));
        Assert.True(running.IsValueUnstarted);
        Assert.True(running.Demand().IsOk);
        Assert.False(whileInFlight);
        Assert.True(running.TryGetCompletedValue(out var seven));
        Assert.Equal(new Result.Atom((Decimal128)7), seven.Value);

        var failed = new NeedCell(() => new EvalError.DivByZero(), () => new(new EvalError.DivByZero()));
        Assert.True(failed.Demand().IsError);
        Assert.False(failed.TryGetCompletedValue(out _));

        var thrown = new NeedCell(() => throw new InvalidOperationException("host"), () => throw new InvalidOperationException("host"));
        Assert.Throws<InvalidOperationException>(() => thrown.Demand());
        Assert.False(thrown.TryGetCompletedValue(out _));

        Assert.True(NeedCell.Ready(new Evaluator.CountedResult(new Result.Atom((Decimal128)3), 1)).TryGetCompletedValue(out var three));
        Assert.Equal(new Result.Atom((Decimal128)3), three.Value);
        Assert.False(NeedCell.Refused(new EvalError.DivByZero(), new Expr.Num((Decimal128)1)).TryGetCompletedValue(out _));

        using var cancellation = new CancellationTokenSource();
        var completed = new NeedCell(() => Value(5), () => new(Value(5)), token: cancellation.Token);
        Assert.True(completed.Demand().IsOk);
        cancellation.Cancel();
        Assert.ThrowsAny<OperationCanceledException>(() => completed.Demand());
        Assert.True(completed.TryGetCompletedValue(out var five));
        Assert.Equal(new Result.Atom((Decimal128)5), five.Value);
    }
}
