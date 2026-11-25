using KatLang.Evaluation;
using KatLang.TestInfrastructure;

namespace KatLang.Tests;

/// <summary>
/// A COMPLETED LIST ELEMENT LETS GO OF ITS SUSPENSION (lazy collections, issue #204; C#-only host policy,
/// 2026-11-25; no Lean counterpart: Lean's deferred cells model no memory). A list literal's deferred
/// element is one VALUE-only cell (<see cref="Evaluator.ElementSuspension"/>): nothing projects its
/// CALLABLE or reifies it, and no plan executes it again, so once its VALUE computation has ended — with a
/// value, an ordinary failure or a stored exception — the cell releases the suspension, which holds the
/// literal's environment (<c>NeedCell.ReleaseElementSuspension</c>). It keeps its outcome, its span, its
/// written source and its identity hash. An element that is a parameter's own cell is that argument's
/// cell, which keeps its suspension and its CALLABLE. The reachability of a loop's literals is guarded by
/// <see cref="LazyStageRetentionTests"/>; these are the cell-level pins, on both families, including
/// genuinely suspending and joined demands.
/// </summary>
public sealed class LiteralElementReleaseTests
{
    private static readonly TimeSpan WaitLimit = TimeSpan.FromSeconds(30);

    private static Evaluator.EvalCtx SynchronousCtx()
        => Evaluator.EvalCtx.Empty with { CallStack = [BuiltinRegistry.CreateRuntimePreludeAlgorithm()] };

    // A context of an asynchronous run whose host operations are `operations`.
    private static Evaluator.EvalCtx AsynchronousCtx(HostOperations operations, CancellationToken token = default)
    {
        var budget = EvaluationBudget.Create(null, operations, cancellationToken: token);
        budget.MarkAsynchronousRun();
        return Evaluator.EvalCtx.Empty with
        {
            Budget = budget,
            CallStack = [operations.RuntimePreludeAlgorithm],
            Services = Evaluator.RunServices.Unconfigured with
            {
                EnableLoopOptimization = false,
                EnableSequencePipelineOptimization = false,
                ZeroArgPropertyResultCache = new KatLang.Evaluation.Caching.RunScopedAsyncZeroArgPropertyResultCache(),
            },
        };
    }

    // The cells of a literal's deferred positions (a constant's slot is its value), built without
    // reading any of them.
    private static NeedCell[] ElementCells(string source, Evaluator.EvalCtx ctx, HostOperations? operations = null)
    {
        Algorithm.User root;
        if (operations is null)
            root = SourceProvenance.ParseValid(source).Root;
        else
        {
            var parsed = Parser.Parse(source, new RunOptions { HostOperations = operations });
            Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
            root = parsed.Root;
        }

        var built = Evaluator.EvalCounted(new Expr.AlgorithmExpr(root), ctx, []);
        Assert.True(built.IsOk, built.IsError ? built.Error.ToString() : null);
        var positions = Assert.IsAssignableFrom<Evaluator.LazyList>(Assert.IsType<Result.ListValue>(built.Value.Value).Lazy);
        var cells = Enumerable.Range(0, positions.Discovered).Select(positions.Slot).OfType<NeedCell>().ToArray();
        Assert.NotEmpty(cells);
        Assert.All(cells, static cell =>
        {
            Assert.IsType<Evaluator.ElementSuspension>(cell.Suspension);
            Assert.False(cell.HasReleasedSuspension);
            Assert.False(cell.HasCompletedValue);
        });
        return cells;
    }

    private static int Hash(NeedCell cell) => NeedNode.IdentityComparer.Instance.GetHashCode(cell);

    private static async Task<EvalResult<Evaluator.CountedResult>> Demand(NeedCell cell, bool asynchronous)
        => asynchronous ? await cell.DemandAsync() : cell.Demand();

    private static void AssertReleased(NeedCell cell, int hash, Expr? source, SourceSpan? span)
    {
        Assert.Null(cell.Suspension);
        Assert.True(cell.HasReleasedSuspension);
        Assert.True(cell.HasCompletedValue);
        Assert.False(cell.HasValueInFlight);
        Assert.Equal(hash, Hash(cell));
        Assert.Same(source, cell.Source);
        Assert.Equal(span, cell.Span);
        // A list position has no META channel, before the release as after it.
        Assert.IsType<EvalError.NotAnAlgorithm>(Evaluator.ReifyMeta(cell).Error);
    }

    // ── 1. A read element releases; an unread one keeps its suspension ───────────────────────

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task AReadElement_ReleasesItsSuspension_AndKeepsItsValueSpanSourceAndHash(bool asynchronous)
    {
        var cells = ElementCells("[1 + 1, 2 + 2, 3 + 3]", SynchronousCtx());
        var hashes = cells.Select(Hash).ToArray();
        var sources = cells.Select(static cell => cell.Source).ToArray();
        var spans = cells.Select(static cell => cell.Span).ToArray();
        Assert.All(sources, static source => Assert.IsType<Expr.Binary>(source));
        Assert.All(spans, static span => Assert.NotNull(span));
        Assert.IsType<EvalError.NotAnAlgorithm>(Evaluator.ReifyMeta(cells[0]).Error);

        var first = await Demand(cells[0], asynchronous);
        var last = await Demand(cells[2], asynchronous);
        Assert.Equal(new Result.Atom(2), first.Value.Value);
        Assert.Equal(new Result.Atom(6), last.Value.Value);
        AssertReleased(cells[0], hashes[0], sources[0], spans[0]);
        AssertReleased(cells[2], hashes[2], sources[2], spans[2]);

        // The unread position is still to be computed: it keeps the literal's environment.
        Assert.IsType<Evaluator.ElementSuspension>(cells[1].Suspension);
        Assert.False(cells[1].HasReleasedSuspension);
        Assert.Equal(hashes[1], Hash(cells[1]));

        // The outcome is the memo: a later demand and a passive read see the same value.
        Assert.Equal(first.Value, (await Demand(cells[0], !asynchronous)).Value);
        Assert.True(cells[2].TryGetCompletedValue(out var passive));
        Assert.Equal(new Result.Atom(6), passive.Value);
        Assert.Equal(new Result.Atom(4), (await Demand(cells[1], asynchronous)).Value.Value);
        AssertReleased(cells[1], hashes[1], sources[1], spans[1]);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task AnElementThatFails_KeepsItsFailureAndItsSpan_AfterTheRelease(bool asynchronous)
    {
        // The constant `2` is a value slot; the two deferred elements are cells.
        var cells = ElementCells("[2, 1 / 0, 3 + 0]", SynchronousCtx());
        var failing = cells[0];
        var hash = Hash(failing);
        var source = failing.Source;
        var span = failing.Span;
        var failed = await Demand(failing, asynchronous);
        Assert.True(failed.IsError);
        Assert.Equal(KatLangErrorCode.DivisionByZero, failed.Error.Code);
        // Positioned at the written division, as before the release existed.
        Assert.Equal(span, failed.Error.Span);
        AssertReleased(failing, hash, source, span);

        // The ordinary failure is sticky: every later demand answers the same object.
        var again = await Demand(failing, !asynchronous);
        Assert.Same(failed.Error, again.Error);
        Assert.False(failing.TryGetCompletedValue(out _));
        Assert.Equal(new Result.Atom(3), (await Demand(cells[1], asynchronous)).Value.Value);
    }

    [Fact]
    public void AnElementThatReadsItself_KeepsTheDemandCycle_AfterTheRelease()
    {
        // `M[0]` reads its own position: the re-entering read is the demand cycle, which the
        // element's computation reports as its own outcome.
        var ctx = SynchronousCtx() with
        {
            Services = Evaluator.RunServices.Unconfigured with { ZeroArgPropertyResultCache = new KatLang.Evaluation.Caching.RunScopedZeroArgPropertyResultCache() },
        };
        var parsed = SourceProvenance.ParseValid("M = [M[0] + 1, 2]\nM");
        var built = Evaluator.EvalCounted(new Expr.AlgorithmExpr(parsed.Root), ctx, []);
        var positions = Assert.IsType<Result.ListValue>(built.Value.Value).Lazy!;
        var cell = Assert.IsType<NeedCell>(positions.Slot(0));
        var hash = Hash(cell);
        var (source, span) = (cell.Source, cell.Span);
        var cycle = cell.Demand();
        Assert.Equal(KatLangErrorCode.DemandCycle, cycle.Error.Code);
        AssertReleased(cell, hash, source, span);
        Assert.Same(cycle.Error, cell.Demand().Error);
        Assert.Equal(new Result.Atom(2), positions.Slot(1));
    }

    // ── 2. Genuinely suspending demands: joins, edges, stored exceptions, cancellation ────────

    [Fact]
    public async Task SuspendedElementsJoinedByOtherObservers_ReleaseOnce_AndTheirWaitersFindTheirEdges()
    {
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var calls = 0;
        var operations = HostOperations.Create(HostOperation.CreateAsync("gate", async (_, _) =>
        {
            Interlocked.Increment(ref calls);
            await release.Task;
            return new Result.Atom(10);
        }));
        var ctx = AsynchronousCtx(operations);
        var cells = ElementCells("[gate() + 1, gate() + 2]", ctx, operations);
        var hashes = cells.Select(Hash).ToArray();
        var sources = cells.Select(static cell => cell.Source).ToArray();
        var spans = cells.Select(static cell => cell.Span).ToArray();

        // One computation waits on BOTH elements at once, so its wait-for edges are promoted to a table
        // keyed by the cells' identity hashes; each edge is removed after its element has completed and
        // released its suspension, so it is found only if the hash did not change.
        var started = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var waiter = new NeedCell(
            static () => throw new InvalidOperationException("asynchronous only"),
            async () =>
            {
                var first = cells[0].DemandAsync();
                var second = cells[1].DemandAsync();
                started.SetResult();
                var a = await first;
                var b = await second;
                var sum = new Result.Atom(((Result.Atom)a.Value.Value).Value + ((Result.Atom)b.Value.Value).Value);
                return EvalResult<Evaluator.CountedResult>.Ok(new Evaluator.CountedResult(sum, 1));
            },
            budget: ctx.Budget);
        var outer = waiter.DemandAsync().AsTask();
        await started.Task.WaitAsync(WaitLimit);
        // A second observer joins the first element's flight.
        var joined = cells[0].DemandAsync().AsTask();
        try
        {
            Assert.True(waiter.HasPromotedDependencies);
            Assert.Equal(2, waiter.ActiveDependencyCount);
            Assert.True(cells[0].HasJoinedValueFlight);
            Assert.All(cells, static cell => Assert.IsType<Evaluator.ElementSuspension>(cell.Suspension));
            Assert.Equal(2, Volatile.Read(ref calls));
        }
        finally
        {
            release.SetResult();
        }

        var total = await outer.WaitAsync(WaitLimit);
        Assert.Equal(new Result.Atom(23), total.Value.Value);
        Assert.Equal(new Result.Atom(11), (await joined.WaitAsync(WaitLimit)).Value.Value);
        Assert.Equal(0, waiter.ActiveDependencyCount);
        Assert.Equal(2, calls);
        for (var index = 0; index < cells.Length; index++)
            AssertReleased(cells[index], hashes[index], sources[index], spans[index]);
    }

    [Fact]
    public async Task AHostExceptionStoredByAnElement_IsRethrownAfterTheRelease()
    {
        var thrown = new InvalidOperationException("host failure");
        var operations = HostOperations.Create(HostOperation.CreateAsync("boom", async (_, _) =>
        {
            await Task.Yield();
            throw thrown;
        }));
        var ctx = AsynchronousCtx(operations);
        var cell = ElementCells("[boom() + 1]", ctx, operations)[0];
        var hash = Hash(cell);
        var (source, span) = (cell.Source, cell.Span);
        Assert.Same(thrown, await Assert.ThrowsAsync<InvalidOperationException>(async () => await cell.DemandAsync()));
        AssertReleased(cell, hash, source, span);
        // Stored, never published and never restarted: every observer rethrows the original object.
        Assert.Same(thrown, await Assert.ThrowsAsync<InvalidOperationException>(async () => await cell.DemandAsync()));
        Assert.False(cell.TryGetCompletedValue(out _));
    }

    [Fact]
    public async Task ACancellationReachedWhileAnElementIsComputed_IsStored_AndTheSuspensionReleased()
    {
        using var cancellation = new CancellationTokenSource();
        var operations = HostOperations.Create(HostOperation.CreateAsync("stop", async (_, _) =>
        {
            await Task.Yield();
            cancellation.Cancel();
            cancellation.Token.ThrowIfCancellationRequested();
            return new Result.Atom(1);
        }));
        var ctx = AsynchronousCtx(operations, cancellation.Token);
        var cells = ElementCells("[stop() + 1, 2 + 2]", ctx, operations);
        var hash = Hash(cells[0]);
        var (source, span) = (cells[0].Source, cells[0].Span);
        var cancelled = await Assert.ThrowsAnyAsync<OperationCanceledException>(async () => await cells[0].DemandAsync());
        Assert.Equal(cancellation.Token, cancelled.CancellationToken);
        AssertReleased(cells[0], hash, source, span);
        await Assert.ThrowsAnyAsync<OperationCanceledException>(async () => await cells[0].DemandAsync());
        // The element nobody read keeps its suspension: its computation never started.
        Assert.IsType<Evaluator.ElementSuspension>(cells[1].Suspension);
        Assert.False(cells[1].HasCompletedValue);
    }

    // ── 3. Argument cells and list positions on the six routes ───────────────────────────────

    [Fact]
    public void AnArgumentCell_KeepsItsSuspension_WhileAnElementCellOfTheSameExpressionReleasesIt()
    {
        var ctx = SynchronousCtx();
        var expression = SourceProvenance.ParseValid("{ 6 }").Root.Output[0];
        var argument = Evaluator.SupplyCell(expression, ctx, []);
        var element = Evaluator.SupplyElementCell(expression, ctx, []);
        Assert.Null(element.ProjectCallable().Value);
        Assert.Equal(new Result.Atom(6), argument.Demand().Value.Value);
        Assert.Equal(new Result.Atom(6), element.Demand().Value.Value);

        // The argument's CALLABLE may still be projected over its suspension, and a plan would execute it again.
        Assert.Same(typeof(Evaluator.ExpressionSuspension), argument.Suspension?.GetType());
        Assert.False(argument.HasReleasedSuspension);
        Assert.NotNull(argument.ProjectCallable().Value);
        Assert.Null(element.ProjectCallable().Value);
        Assert.Null(element.Suspension);
        Assert.True(element.HasReleasedSuspension);
    }

    private static async Task Expect(string source, string expected)
    {
        var observation = await SixRouteAgreement.OnEveryRouteAsync(source);
        var outcome = observation.Kind switch
        {
            "ok" => $"ok {observation.Value}",
            "err" => $"err {observation.Errors[0][..observation.Errors[0].IndexOf(':')]}",
            _ => observation.Kind,
        };
        Assert.Equal(expected, outcome);
    }

    [Theory]
    // A parameter that is a literal's element is that argument's own cell: after the literal read its
    // VALUE, the parameter's CALLABLE is still found (a zero-parameter callable given an item).
    [InlineData("Seven = 7\nP(f) = [f][0] + [1].map(f).sum\nP(Seven)", "err ArityMismatch")]
    [InlineData("Seven = 7\nP(f) = [f + 1][0] + [1].map(f).sum\nP(Seven)", "err ArityMismatch")]
    // A list position has no CALLABLE channel, whether or not its VALUE has been read…
    [InlineData("Seven = 7\nP([f]) = [1].map(f).sum\nP([Seven])", "err NotAnAlgorithm")]
    [InlineData("Seven = 7\nP([f]) = f + [1].map(f).sum\nP([Seven])", "err NotAnAlgorithm")]
    // …and no META channel.
    [InlineData("Capture(meta op) = op\nL = [1 + 1]\nL[0] + 0, Capture(L[0])", "err NotAnAlgorithm")]
    // Completed elements keep their values and failures for every later reader.
    [InlineData("L = [tick(), 1 / 0, tick() * 10]\nL[2] + L[0], L.count, L[0], tick()", "ok S[12, 3, 2, 3]")]
    [InlineData("L = [tick(), 1 / 0]\nL[0], L[1]", "err DivisionByZero")]
    [InlineData("M = [M[1] + 1, 2]\nM, M[0]", "ok S[L[3, 2], 3]")]
    [InlineData("M = [M[0] + 1, 2]\nM[1], M", "err DemandCycle")]
    // A nested literal read through a shared outer list.
    [InlineData("Inner = [tick(), tick()]\nOuter = [Inner, [Inner[1] * 10]]\nOuter[1][0], Outer[0], Outer, tick()", "ok S[10, L[3, 1], L[L[3, 1], L[10]], 2]")]
    public async Task ListPositions_KeepTheirChannelsAndOutcomes_OnEveryRoute(string source, string expected)
        => await Expect(source, expected);

    // ── 4. The release costs no space in a cell and no allocation ─────────────────────────────

    [Fact]
    public void ReleasingAnElement_AddsNoSizeToACell_AndAllocatesNothingBeyondTheDemand_GcIsolatedChild()
    {
        if (!GcIsolatedAllocation.EnterChild())
            return;

        // The kept hash lives in the cell's tail padding and the flag beside `_ready`: a cell is as
        // large as it was before the release existed (200 bytes on a 64-bit runtime).
        if (Environment.Is64BitProcess)
            Assert.Equal(200, InstanceSize.Of(typeof(NeedCell)));

        // A completed element and a completed argument of one expression allocate the same: the
        // release itself (the kept hash, the flag, the cleared field) allocates nothing.
        var ctx = SynchronousCtx();
        var expression = SourceProvenance.ParseValid("2 * 3").Root.Output[0];
        _ = Evaluator.SupplyCell(expression, ctx, []).Demand();
        _ = Evaluator.SupplyElementCell(expression, ctx, []).Demand();
        var argument = Evaluator.SupplyCell(expression, ctx, []);
        var element = Evaluator.SupplyElementCell(expression, ctx, []);
        var before = GC.GetAllocatedBytesForCurrentThread();
        var argumentValue = argument.Demand();
        var argumentBytes = GC.GetAllocatedBytesForCurrentThread() - before;
        before = GC.GetAllocatedBytesForCurrentThread();
        var elementValue = element.Demand();
        var elementBytes = GC.GetAllocatedBytesForCurrentThread() - before;
        Assert.Equal(argumentValue.Value, elementValue.Value);
        Assert.True(element.HasReleasedSuspension);
        Assert.Equal(argumentBytes, elementBytes);
        GcIsolatedAllocation.Complete();
    }
}
