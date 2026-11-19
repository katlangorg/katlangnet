using System.Diagnostics;
using System.Numerics;
using System.Reflection;
using System.Runtime.CompilerServices;
using KatLang.Evaluation;
using KatLang.TestInfrastructure;

namespace KatLang.Tests;

/// <summary>
/// The remaining per-demand allocations of call-by-need (2026-11-19, C# implementation only). A node
/// holds its first wait-for edge inline and promotes its edges to a table only for a second distinct
/// target, so the graph stays exact: every registration counts, and every cycle check sees both forms.
/// A cell's gate is its own monitor, and the graph's identity tables never write a cell's object
/// header, so that monitor stays a thin lock. A runtime CALLABLE projection's shared completion is
/// created by its first joiner, as the VALUE flight's is. Overlap is established by observed state,
/// never by a delay; the bounded waits are hang guards.
/// </summary>
public class NeedCellEdgesAndGateTests
{
    private static readonly TimeSpan WaitLimit = TimeSpan.FromSeconds(30);

    private static readonly EvalResult<Evaluator.CountedResult> Seven
        = EvalResult<Evaluator.CountedResult>.Ok(new(new Result.Atom(7), 1));

    private static readonly EvalResult<Algorithm?> Nothing = EvalResult<Algorithm?>.Ok(null);

    private static NeedCell Node(EvaluationBudget budget) => new(static () => Seven, static () => new(Seven), budget: budget);

    private static async Task Until(Func<bool> condition)
    {
        var deadline = DateTime.UtcNow + WaitLimit;
        while (!condition())
        {
            Assert.True(DateTime.UtcNow < deadline, "The awaited condition did not hold in time.");
            await Task.Delay(5);
        }
    }

    // ── Edge multiplicity (NeedNode.AddDependency, RemoveDependency, ReachesLocked) ────────────────
    // `child.AddDependency(parent)` registers the edge parent→child; it refuses an edge that closes a cycle.

    [Fact]
    public void EdgeMultiplicity_SurvivesPromotion_AndEveryCycleCheckSeesBothForms()
    {
        var budget = EvaluationBudget.Create(null);
        var a = Node(budget);
        var b = Node(budget);
        var c = Node(budget);
        var p = Node(budget);

        // A→B twice: one inline edge registered twice.
        Assert.True(b.AddDependency(a));
        Assert.True(b.AddDependency(a));
        Assert.Equal(1, a.ActiveDependencyCount);
        Assert.False(a.HasPromotedDependencies);
        // A→C: a second distinct target promotes both edges, with their multiplicities.
        Assert.True(c.AddDependency(a));
        Assert.True(a.HasPromotedDependencies);
        Assert.Equal(2, a.ActiveDependencyCount);
        // P→A is inline in front of the promoted node: B→P and C→P close cycles through both forms.
        Assert.True(a.AddDependency(p));
        Assert.False(p.HasPromotedDependencies);
        Assert.False(p.AddDependency(b));
        Assert.False(p.AddDependency(c));
        a.RemoveDependency(p);
        Assert.Equal(0, p.ActiveDependencyCount);

        // Removing one A→B registration keeps the other, so B→A is still a cycle.
        b.RemoveDependency(a);
        Assert.Equal(2, a.ActiveDependencyCount);
        Assert.False(a.AddDependency(b));
        // Removing the second ends the edge: B→A is accepted, and A→C is still present.
        b.RemoveDependency(a);
        Assert.Equal(1, a.ActiveDependencyCount);
        Assert.True(a.AddDependency(b));
        Assert.Equal(1, b.ActiveDependencyCount);
        Assert.False(a.AddDependency(c)); // C→A would close A→C
        Assert.False(b.AddDependency(c)); // C→B would close B→A→C (inline, then the promoted table)

        a.RemoveDependency(b);
        c.RemoveDependency(a);
        Assert.All(new[] { a, b, c, p }, node => Assert.Equal(0, node.ActiveDependencyCount));
        // A promoted node keeps its (now empty) table; every other node never had one.
        Assert.True(a.HasPromotedDependencies);
        Assert.All(new[] { b, c, p }, node => Assert.False(node.HasPromotedDependencies));
    }

    [Fact]
    public void EdgeMultiplicity_OfADuplicateRegistration_StaysInline()
    {
        var budget = EvaluationBudget.Create(null);
        var a = Node(budget);
        var b = Node(budget);

        Assert.True(b.AddDependency(a));
        Assert.True(b.AddDependency(a));
        Assert.Equal(1, a.ActiveDependencyCount);
        b.RemoveDependency(a);
        Assert.Equal(1, a.ActiveDependencyCount);
        Assert.False(a.AddDependency(b)); // B→A while one A→B registration is active
        b.RemoveDependency(a);
        Assert.Equal(0, a.ActiveDependencyCount);
        Assert.True(a.AddDependency(b)); // and accepted once none is
        a.RemoveDependency(b);

        Assert.All(new[] { a, b }, node =>
        {
            Assert.Equal(0, node.ActiveDependencyCount);
            Assert.False(node.HasPromotedDependencies);
        });
        // A removal without its registration is a broken invariant, never a silent no-op.
        Assert.Throws<UnreachableException>(() => b.RemoveDependency(a));
    }

    /// <summary>
    /// The same forms through real demands: one parent's asynchronous computation starts two demands
    /// before awaiting either. Two demands of one child (the second joins the first's flight) are one
    /// inline edge registered twice; demands of two children promote the parent's edges. In both, a
    /// child→parent edge is refused while any registration is active, and every edge is gone afterwards.
    /// </summary>
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task OverlappingDemandsOfOneParent_KeepItsEdgesExact(bool distinctChildren)
    {
        var budget = EvaluationBudget.Create(null);
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        NeedCell Child() => new(() => throw new InvalidOperationException(), async () =>
        {
            await release.Task;
            return Seven;
        }, budget: budget);
        var first = Child();
        var second = distinctChildren ? Child() : first;
        NeedCell? parent = null;
        var activeEdges = 0;
        var promoted = false;
        var refused = new List<bool>();
        parent = new NeedCell(() => throw new InvalidOperationException(), async () =>
        {
            var one = first.DemandAsync().AsTask();
            var two = second.DemandAsync().AsTask();
            activeEdges = parent!.ActiveDependencyCount;
            promoted = parent.HasPromotedDependencies;
            refused.Add(!parent.AddDependency(first));
            refused.Add(!parent.AddDependency(second));
            release.SetResult();
            var outcomes = await Task.WhenAll(one, two);
            return outcomes[0].IsError ? outcomes[0] : outcomes[1];
        }, budget: budget);

        var outcome = await parent.DemandAsync().AsTask().WaitAsync(WaitLimit);

        Assert.True(outcome.IsOk, outcome.IsError ? outcome.Error.ToString() : null);
        Assert.Equal(distinctChildren ? 2 : 1, activeEdges);
        Assert.Equal(distinctChildren, promoted);
        Assert.Equal([true, true], refused);
        Assert.All(new[] { parent, first, second }, cell => Assert.Equal(0, cell.ActiveDependencyCount));
        Assert.False(NeedNode.HasCurrentNode);
    }

    // ── The gate is the cell's own monitor ─────────────────────────────────────────────────────────

    /// <summary>
    /// An identity-only CALLABLE projection runs under the cell gate, and inside it the cell's own
    /// monitor is held; a VALUE computation and a runtime projection run outside the gate, where it is
    /// not. Reflective race adapters (<c>NeedCellTests.ObserverArrivingDuringCompletion…</c>) lock the
    /// cell itself on this basis.
    /// </summary>
    [Fact]
    public void TheCellsOwnMonitor_IsTheGate()
    {
        var budget = EvaluationBudget.Create(null);
        NeedCell? cell = null, runtime = null;
        bool? underIdentityProjection = null, underValue = null, underRuntimeProjection = null;
        cell = new NeedCell(() => { underValue = Monitor.IsEntered(cell!); return Seven; }, () => new(Seven),
            () => { underIdentityProjection = Monitor.IsEntered(cell!); return Nothing; }, budget: budget);
        runtime = NeedCell.WithRuntimeProjection(() => Seven, () => new(Seven),
            () => { underRuntimeProjection = Monitor.IsEntered(runtime!); return Nothing; }, () => new(Nothing), budget: budget);

        Assert.True(cell.ProjectCallable().IsOk);
        Assert.True(cell.Demand().IsOk);
        Assert.True(runtime.ProjectCallable().IsOk);

        Assert.True(underIdentityProjection);
        Assert.False(underValue);
        Assert.False(underRuntimeProjection);
        Assert.False(Monitor.IsEntered(cell));
        Assert.False(Monitor.IsEntered(runtime));
    }

    // ── Runtime projection: single flight with a lazily created completion ─────────────────────────

    public enum Ending { Identity, HostException, Cancellation }

    public static TheoryData<bool, bool, Ending> JoinCases()
    {
        var data = new TheoryData<bool, bool, Ending>();
        foreach (var starter in new[] { false, true })
            foreach (var joiner in new[] { false, true })
                foreach (var ending in Enum.GetValues<Ending>())
                    data.Add(starter, joiner, ending);
        return data;
    }

    /// <summary>
    /// A running runtime projection nobody joined has no shared completion; the first joiner creates it
    /// and waits on it. Both observers receive the one computation's outcome: its identity, or the
    /// original host exception or cancellation (the object and its token).
    /// </summary>
    [Theory]
    [MemberData(nameof(JoinCases))]
    public async Task ASecondObserver_CreatesTheProjectionsSharedCompletion_AndJoinsTheOneComputation(
        bool asynchronousStarter, bool asynchronousJoiner, Ending ending)
    {
        using var host = new CancellationTokenSource();
        var identity = new Algorithm.Builtin(BuiltinId.@count);
        Exception? thrown = ending switch
        {
            Ending.HostException => new InvalidOperationException("original host failure"),
            Ending.Cancellation => new OperationCanceledException("host cancellation", host.Token),
            _ => null,
        };
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var starts = 0;
        var unjoinedInside = false;
        NeedCell? cell = null;
        void Enter()
        {
            Interlocked.Increment(ref starts);
            unjoinedInside = cell!.HasProjectionInFlight && !cell.HasJoinedProjectionFlight;
            entered.SetResult();
        }
        EvalResult<Algorithm?> Finish() => thrown is null ? EvalResult<Algorithm?>.Ok(identity) : throw thrown;
        cell = NeedCell.WithRuntimeProjection(() => Seven, () => new(Seven), () =>
        {
            Enter();
            release.Task.WaitAsync(WaitLimit).GetAwaiter().GetResult();
            return Finish();
        }, async () =>
        {
            Enter();
            await release.Task.WaitAsync(WaitLimit);
            return Finish();
        }, budget: EvaluationBudget.Create(null));

        Task<EvalResult<Algorithm?>> Observe(bool asynchronous) => asynchronous
            ? Task.Run(async () => await cell.ProjectCallableAsync())
            : Task.Factory.StartNew(() => cell.ProjectCallable(), CancellationToken.None,
                TaskCreationOptions.LongRunning, TaskScheduler.Default);
        var starter = Observe(asynchronousStarter);
        await entered.Task.WaitAsync(WaitLimit);
        Assert.True(unjoinedInside);
        Assert.False(cell.HasJoinedProjectionFlight);

        var joiner = Observe(asynchronousJoiner);
        await Until(() => cell.HasJoinedProjectionFlight || joiner.IsCompleted);
        Assert.False(joiner.IsCompleted);
        Assert.True(cell.HasProjectionInFlight);
        release.SetResult();

        foreach (var observer in new[] { starter, joiner })
        {
            if (thrown is null)
            {
                Assert.Same(identity, (await observer.WaitAsync(WaitLimit)).Value);
                continue;
            }
            var error = await Assert.ThrowsAnyAsync<Exception>(() => observer.WaitAsync(WaitLimit));
            Assert.Same(thrown, error);
            if (error is OperationCanceledException cancelled) Assert.Equal(host.Token, cancelled.CancellationToken);
        }
        Assert.Equal(1, starts);
        Assert.Equal(1, cell.ProjectionComputations);
        Assert.False(cell.HasProjectionInFlight);
        Assert.False(cell.HasJoinedProjectionFlight);
        Assert.Equal(thrown is null, cell.HasCallableMemo);
        Assert.Equal(0, cell.ProjectionActiveDependencyCount);
    }

    /// <summary>
    /// A runtime projection's starter nobody joined still rethrows the original host exception and
    /// cancellation (the object and its token), exactly as awaiting a shared completion delivered
    /// them; the stored exception stays sticky for every later observation.
    /// </summary>
    [Theory]
    [InlineData(false, false)]
    [InlineData(false, true)]
    [InlineData(true, false)]
    [InlineData(true, true)]
    public async Task AnUnjoinedProjectionStarter_RethrowsTheOriginalExceptionAndToken(bool asynchronous, bool cancellation)
    {
        using var host = new CancellationTokenSource();
        Exception thrown = cancellation
            ? new OperationCanceledException("host cancellation", host.Token)
            : new InvalidOperationException("original host failure");
        var starts = 0;
        var cell = NeedCell.WithRuntimeProjection(() => Seven, () => new(Seven),
            () => { starts++; throw thrown; },
            () => { starts++; throw thrown; },
            budget: EvaluationBudget.Create(null));

        var first = asynchronous
            ? await Assert.ThrowsAnyAsync<Exception>(() => cell.ProjectCallableAsync().AsTask())
            : Assert.ThrowsAny<Exception>(() => cell.ProjectCallable());
        Assert.Same(thrown, first);
        if (first is OperationCanceledException cancelled) Assert.Equal(host.Token, cancelled.CancellationToken);
        Assert.Same(thrown, Assert.ThrowsAny<Exception>(() => cell.ProjectCallable()));
        Assert.Same(thrown, await Assert.ThrowsAnyAsync<Exception>(() => cell.ProjectCallableAsync().AsTask()));
        Assert.Equal(1, starts);
        Assert.False(cell.HasProjectionInFlight);
        Assert.False(cell.HasCallableMemo);
        Assert.False(NeedNode.HasCurrentNode);
    }

    // ── Strict allocation counts (isolated child processes) ────────────────────────────────────────

    private static long Bytes(Action action)
    {
        var before = GC.GetAllocatedBytesForCurrentThread();
        action();
        return GC.GetAllocatedBytesForCurrentThread() - before;
    }

    // One instance of the type, with nothing else.
    private static long InstanceBytes(Type type)
    {
        _ = RuntimeHelpers.GetUninitializedObject(type);
        return Bytes(() => _ = RuntimeHelpers.GetUninitializedObject(type));
    }

    // An async method's own state machine: a struct in an optimized build, which a synchronous
    // completion never boxes, but a heap class in a Debug build (one object per call).
    private static long StateMachineBytes(Type owner, string method)
    {
        var type = owner.GetMethod(method, BindingFlags.NonPublic | BindingFlags.Instance | BindingFlags.Static)!
            .GetCustomAttribute<AsyncStateMachineAttribute>()!.StateMachineType;
        return type.IsValueType ? 0 : InstanceBytes(type);
    }

    private static T CompleteSynchronously<T>(ValueTask<T> operation)
    {
        Assert.True(operation.IsCompletedSuccessfully, "The operation must complete without suspension.");
        return operation.Result;
    }

    // The logical context the computation sets and clears, on the measuring thread.
    private static long ContextBytes()
    {
        var current = new AsyncLocal<object?>();
        var node = new object();
        return Bytes(() =>
        {
            current.Value = node;
            current.Value = null;
        });
    }

    [Fact]
    public void ACell_IsItsOwnGate_AndAllocatesNothingBesideItself_GcIsolatedChild()
    {
        if (!GcIsolatedAllocation.EnterChild())
            return;

        var budget = EvaluationBudget.Create(null);
        var value = Seven.Value;
        _ = NeedCell.Ready(value); // warm-up
        _ = Node(budget);
        var cell = InstanceBytes(typeof(NeedCell));
        Assert.Equal(cell, Bytes(() => _ = NeedCell.Ready(value)));
        Assert.Equal(cell, Bytes(() => _ = Node(budget)));
        GcIsolatedAllocation.Complete();
    }

    [Fact]
    public void AnUnjoinedRuntimeProjection_AllocatesNoCompletion_GcIsolatedChild()
    {
        if (!GcIsolatedAllocation.EnterChild())
            return;

        var budget = EvaluationBudget.Create(null);
        NeedCell Fresh() => NeedCell.WithRuntimeProjection(static () => Seven, static () => new(Seven),
            static () => Nothing, static () => new(Nothing), budget: budget);
        _ = Fresh().ProjectCallable(); // warm-up
        _ = CompleteSynchronously(Fresh().ProjectCallableAsync());

        var synchronous = Fresh();
        Assert.Equal(ContextBytes(), Bytes(() => _ = synchronous.ProjectCallable()));
        var asynchronous = Fresh();
        var expected = StateMachineBytes(typeof(NeedCell), "ProjectRuntimeAsync")
            + StateMachineBytes(typeof(NeedCell), "ProjectRuntimeComputationAsync")
            + ContextBytes();
        Assert.Equal(expected, Bytes(() => _ = CompleteSynchronously(asynchronous.ProjectCallableAsync())));

        Assert.All(new[] { synchronous, asynchronous }, cell =>
        {
            Assert.True(cell.HasCallableMemo);
            Assert.False(cell.HasProjectionInFlight);
            Assert.Equal(1, cell.ProjectionComputations);
        });
        Assert.False(NeedNode.HasCurrentNode);
        GcIsolatedAllocation.Complete();
    }

    /// <summary>
    /// A cell keyed by a resolution record (both channels) and by a promoted edge table still locks
    /// with a thin monitor: those tables hash the cell without writing its object header. The control
    /// shows the measurement sees an inflated monitor: a header that holds the identity hash makes the
    /// next lock allocate one.
    /// </summary>
    [Fact]
    public void ACellTheGraphTablesKeyed_StillLocksWithoutAllocating_GcIsolatedChild()
    {
        if (!GcIsolatedAllocation.EnterChild())
            return;

        var budget = EvaluationBudget.Create(null);
        // The production forms: a written argument's cell and a host-built cell with a projection.
        var written = Evaluator.SupplyCell(new Expr.Num(5), Evaluator.EvalCtx.Empty with { Budget = budget }, []);
        var hostBuilt = new NeedCell(static () => Seven, static () => new(Seven), static () => Nothing, budget: budget);
        var parent = Node(budget);
        var record = new NeedCell.ResolutionRecord();
        record.RecordValue(written, Seven);
        record.RecordCallable(hostBuilt, Nothing);
        Assert.True(record.Contains(written, NeedCell.Channel.Value));
        Assert.True(record.TryGetCallable(hostBuilt, out _));
        Assert.True(written.AddDependency(parent));
        Assert.True(hostBuilt.AddDependency(parent));
        Assert.True(parent.HasPromotedDependencies);
        Assert.False(parent.AddDependency(hostBuilt)); // the cycle check walks the promoted table

        _ = Node(budget).HasCompletedValue; // warm-up
        foreach (var cell in new[] { written, hostBuilt })
            Assert.Equal(0, Bytes(() => _ = cell.HasCompletedValue));
        var control = Node(budget);
        _ = RuntimeHelpers.GetHashCode(control);
        Assert.True(Bytes(() => _ = control.HasCompletedValue) > 0, "the control's lock should allocate an inflated monitor");

        written.RemoveDependency(parent);
        hostBuilt.RemoveDependency(parent);
        Assert.Equal(0, parent.ActiveDependencyCount);
        GcIsolatedAllocation.Complete();
    }
}
