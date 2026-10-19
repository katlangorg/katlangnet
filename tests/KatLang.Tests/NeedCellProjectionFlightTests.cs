using System.Numerics;
using System.Reflection;
using System.Runtime.ExceptionServices;
using KatLang.Evaluation;

namespace KatLang.Tests;

/// <summary>
/// The CALLABLE channel's runtime projection control (META-S3-0a): ONE wait-for graph for both
/// channels and the VALUE single-flight protocol on a cell's projection node (NEED-09; Lean
/// <c>NeedProjection.step</c>, <c>KatLangArityLaws/NeedControl.lean</c> § Projection). No source
/// program builds a runtime projection yet, so every case drives the production machinery through
/// the internal construction point <see cref="NeedCell.WithRuntimeProjection"/> with delegate
/// computations that choose exactly which VALUE demands and CALLABLE projections they perform.
/// <para>Overlap is established by observed state, never by a settle delay: a computation signals
/// its entry, the independent observer's wait-for edge is observed before the computation is
/// released, and computation attempts are counted separately from retained outcomes. The bounded
/// waits are hang guards, never latency claims.</para>
/// </summary>
public sealed class NeedCellProjectionFlightTests
{
    private static readonly TimeSpan WaitLimit = TimeSpan.FromSeconds(30);
    private static readonly SourceSpan SpanA = new(2, 3, 2, 4);
    private static readonly SourceSpan SpanB = new(3, 3, 3, 4);
    private static readonly SourceSpan SpanC = new(4, 3, 4, 4);

    private static EvalResult<Evaluator.CountedResult> Value(int number = 1)
        => EvalResult<Evaluator.CountedResult>.Ok(new(new Result.Atom((Decimal128)number), 1));

    private static EvalResult<Algorithm?> Identity(Algorithm algorithm) => EvalResult<Algorithm?>.Ok(algorithm);

    private static NeedCell Runtime(EvaluationBudget budget, Func<EvalResult<Algorithm?>> project,
        Func<ValueTask<EvalResult<Algorithm?>>>? projectAsync = null, SourceSpan? span = null,
        CancellationToken token = default, Func<EvalResult<Evaluator.CountedResult>>? value = null)
        => NeedCell.WithRuntimeProjection(value ?? (() => Value()), () => new(value?.Invoke() ?? Value()),
            project, projectAsync ?? (() => new(project())), span, budget, token);

    private static NeedCell ValueCell(EvaluationBudget budget, Func<EvalResult<Evaluator.CountedResult>> evaluate,
        Func<ValueTask<EvalResult<Evaluator.CountedResult>>>? evaluateAsync = null, SourceSpan? span = null)
        => new(evaluate, evaluateAsync ?? (() => new(evaluate())), span: span, budget: budget);

    private static EvalResult<Algorithm?> AsCallable(EvalResult<Evaluator.CountedResult> value, Algorithm algorithm)
        => value.IsError ? value.Error : Identity(algorithm);

    private static async Task Until(Func<bool> condition)
    {
        var deadline = DateTime.UtcNow + WaitLimit;
        while (!condition())
        {
            if (DateTime.UtcNow > deadline) throw new TimeoutException("controlled-overlap handshake");
            await Task.Delay(1);
        }
    }

    // ── One graph: cycles and noncyclic dependencies ──────────────────────────────────────────

    [Fact]
    public async Task CallableSelfCycle_IsDemandCycleAtTheCellsSpan_StickyAndCleaned()
    {
        foreach (var asynchronous in new[] { false, true })
        {
            var budget = EvaluationBudget.Create(null);
            NeedCell? a = null;
            a = Runtime(budget, () => a!.ProjectCallable(),
                async () => { await Task.Yield(); return await a!.ProjectCallableAsync(); }, SpanA);
            var first = asynchronous ? await a.ProjectCallableAsync().AsTask().WaitAsync(WaitLimit) : a.ProjectCallable();
            var cycle = Assert.IsType<EvalError.DemandCycle>(first.Error);
            Assert.Equal(SpanA, cycle.Span);
            Assert.Equal(1, a.ProjectionComputations);
            Assert.True(a.HasCallableMemo);
            // The propagated cycle is the computation's own sticky outcome (VALUE parity).
            Assert.Same(cycle, a.ProjectCallable().Error);
            Assert.Same(cycle, (await a.ProjectCallableAsync()).Error);
            Assert.Equal(1, a.ProjectionComputations);
            Assert.Equal(0, a.ProjectionActiveDependencyCount);
            Assert.False(a.HasProjectionInFlight);
            Assert.False(a.HasCompletedValue);
            Assert.False(NeedNode.HasCurrentNode);
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task ReentryDoesNotPublishOrCompleteTheActiveFlight(bool asynchronous)
    {
        var budget = EvaluationBudget.Create(null);
        var count = new Algorithm.Builtin(BuiltinId.@count);
        var reentered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        NeedCell? cell = null;
        void CheckReentry(EvalResult<Algorithm?> result)
        {
            Assert.Equal(SpanA, Assert.IsType<EvalError.DemandCycle>(result.Error).Span);
            Assert.True(cell!.HasProjectionInFlight);
            Assert.False(cell.HasCallableMemo);
            Assert.Equal(1, cell.ProjectionComputations);
            Assert.Equal(0, cell.ProjectionActiveDependencyCount);
            Assert.True(NeedNode.HasCurrentNode);
            reentered.SetResult();
        }
        cell = Runtime(budget, () =>
        {
            CheckReentry(cell!.ProjectCallable());
            release.Task.WaitAsync(WaitLimit).GetAwaiter().GetResult();
            return Identity(count);
        }, async () =>
        {
            await Task.Yield();
            CheckReentry(await cell!.ProjectCallableAsync());
            await release.Task.WaitAsync(WaitLimit);
            return Identity(count);
        }, SpanA);
        var parent = ValueCell(budget, () =>
        {
            Assert.Same(count, cell.ProjectCallable().Value);
            return Value();
        }, async () =>
        {
            Assert.Same(count, (await cell.ProjectCallableAsync()).Value);
            return Value();
        });
        var starter = Task.Run(async () => asynchronous ? await cell.ProjectCallableAsync() : cell.ProjectCallable());
        Task<EvalResult<Evaluator.CountedResult>>? waiter = null;
        try
        {
            await reentered.Task.WaitAsync(WaitLimit);
            waiter = Task.Run(async () => asynchronous ? await parent.DemandAsync() : parent.Demand());
            await Until(() => parent.ActiveDependencyCount == 1 || waiter.IsCompleted);
            Assert.False(waiter.IsCompleted);
            Assert.False(cell.HasCallableMemo);
            Assert.True(cell.HasProjectionInFlight);
        }
        finally { release.TrySetResult(); }

        Assert.Same(count, (await starter.WaitAsync(WaitLimit)).Value);
        Assert.True((await waiter!.WaitAsync(WaitLimit)).IsOk);
        Assert.Same(count, cell.ProjectCallable().Value);
        Assert.Same(count, (await cell.ProjectCallableAsync()).Value);
        Assert.Equal(1, cell.ProjectionComputations);
        Assert.False(cell.HasProjectionInFlight);
        Assert.False(cell.HasCompletedValue);
        Assert.Equal(0, cell.ProjectionActiveDependencyCount);
        Assert.Equal(0, parent.ActiveDependencyCount);
        Assert.False(NeedNode.HasCurrentNode);
    }

    [Theory]
    [InlineData(2)]
    [InlineData(3)]
    public void CallableCycleOfSeveralCells_BlamesTheReenteredCell(int length)
    {
        var budget = EvaluationBudget.Create(null);
        var spans = new[] { SpanA, SpanB, SpanC };
        var cells = new NeedCell[length];
        for (var i = 0; i < length; i++)
        {
            var next = (i + 1) % length;
            cells[i] = Runtime(budget, () => cells[next].ProjectCallable(), span: spans[i]);
        }
        var result = cells[0].ProjectCallable();
        Assert.Equal(SpanA, Assert.IsType<EvalError.DemandCycle>(result.Error).Span);
        Assert.All(cells, cell =>
        {
            Assert.Equal(1, cell.ProjectionComputations);
            Assert.True(cell.HasCallableMemo);
            Assert.Equal(0, cell.ProjectionActiveDependencyCount);
            Assert.Equal(KatLangErrorCode.DemandCycle, cell.ProjectCallable().Error.Code);
        });
        Assert.Equal(1, cells[^1].ProjectionComputations);
        Assert.False(NeedNode.HasCurrentNode);
    }

    [Fact]
    public void ValueCallableValue_IsDemandCycle_AndBothChannelsKeepTheirOutcome()
    {
        // V(R) → C(A) → V(R): R's VALUE projects A, whose runtime projection demands R.
        var budget = EvaluationBudget.Create(null);
        var count = new Algorithm.Builtin(BuiltinId.@count);
        NeedCell? a = null;
        var evaluations = 0;
        var r = ValueCell(budget, () =>
        {
            evaluations++;
            var projected = a!.ProjectCallable();
            return projected.IsError ? projected.Error : Value();
        }, span: SpanB);
        a = Runtime(budget, () => AsCallable(r.Demand(), count), span: SpanA);
        var result = r.Demand();
        Assert.Equal(SpanB, Assert.IsType<EvalError.DemandCycle>(result.Error).Span);
        Assert.Equal(1, evaluations);
        Assert.Equal(1, a.ProjectionComputations);
        // A's projection received the cycle and published it; R's VALUE then completed with it.
        Assert.Same(result.Error, a.ProjectCallable().Error);
        Assert.Same(result.Error, r.Demand().Error);
        Assert.False(a.HasCompletedValue);
        Assert.Equal(0, r.ActiveDependencyCount);
        Assert.Equal(0, a.ProjectionActiveDependencyCount);
    }

    [Fact]
    public void CallableValueCallable_IsDemandCycle_WithoutRunawayRecursion()
    {
        // C(A) → V(R) → C(A): the re-entry goes through a VALUE node of the same graph.
        var budget = EvaluationBudget.Create(null);
        var count = new Algorithm.Builtin(BuiltinId.@count);
        NeedCell? a = null;
        var evaluations = 0;
        var r = ValueCell(budget, () =>
        {
            evaluations++;
            var projected = a!.ProjectCallable();
            return projected.IsError ? projected.Error : Value();
        }, span: SpanB);
        a = Runtime(budget, () => AsCallable(r.Demand(), count), span: SpanA);
        var result = a.ProjectCallable();
        Assert.Equal(SpanA, Assert.IsType<EvalError.DemandCycle>(result.Error).Span);
        Assert.Equal(1, evaluations);
        Assert.Equal(1, a.ProjectionComputations);
        Assert.Equal(KatLangErrorCode.DemandCycle, r.Demand().Error.Code);
        Assert.Equal(1, evaluations);
        Assert.Equal(0, r.ActiveDependencyCount);
        Assert.Equal(0, a.ProjectionActiveDependencyCount);
    }

    [Fact]
    public void CallableToCallable_SharesTheProjectedIdentity_AndRecordsEdgesWhileActive()
    {
        var budget = EvaluationBudget.Create(null);
        var count = new Algorithm.Builtin(BuiltinId.@count);
        var receiverEvaluations = 0;
        int? edgesDuringReceiver = null;
        NeedCell? b = null;
        var receiver = ValueCell(budget, () =>
        {
            receiverEvaluations++;
            edgesDuringReceiver = b!.ProjectionActiveDependencyCount;
            return Value();
        });
        b = Runtime(budget, () =>
        {
            // The VALUE cell's evaluation is not this projection: the channels are distinct nodes.
            Assert.False(receiver.IsEvaluatingInCurrentFlow());
            return AsCallable(receiver.Demand(), count);
        });
        var a = Runtime(budget, () => b.ProjectCallable());
        Assert.Same(count, a.ProjectCallable().Value);
        Assert.Equal(1, edgesDuringReceiver);   // CALLABLE → VALUE edge recorded while it waits
        Assert.Same(count, b.ProjectCallable().Value);
        Assert.Equal(1, a.ProjectionComputations);
        Assert.Equal(1, b.ProjectionComputations);
        Assert.Equal(1, receiverEvaluations);
        Assert.False(a.HasCompletedValue);
        Assert.False(b.HasCompletedValue);
        Assert.Equal(0, a.ProjectionActiveDependencyCount);
        Assert.Equal(0, b.ProjectionActiveDependencyCount);
    }

    [Fact]
    public void CompletedReceiverFollowedByRecursiveProjection_IsDemandCycle()
    {
        var budget = EvaluationBudget.Create(null);
        var receiver = ValueCell(budget, () => Value());
        Assert.True(receiver.Demand().IsOk);
        NeedCell? a = null;
        a = Runtime(budget, () =>
        {
            var value = receiver.Demand();
            return value.IsError ? value.Error : a!.ProjectCallable();
        }, span: SpanA);
        Assert.Equal(SpanA, Assert.IsType<EvalError.DemandCycle>(a.ProjectCallable().Error).Span);
        Assert.Equal(1, a.ProjectionComputations);
        Assert.Equal(0, a.ProjectionActiveDependencyCount);
    }

    [Fact]
    public void TransportedParameterCell_KeepsOneProjectionNode()
    {
        // Parameter transport hands over the SAME cell, so a runtime projection reached through
        // any number of transports is one node: projecting it from inside itself is a cycle, and
        // an identity-only parameter cell projected from a runtime projection is no dependency.
        var budget = EvaluationBudget.Create(null);
        var count = new Algorithm.Builtin(BuiltinId.@count);
        var leafProjections = 0;
        var leaf = new NeedCell(() => Value(), () => new(Value()),
            () => { leafProjections++; return Identity(count); }, span: SpanB, budget: budget);
        var ctx = Evaluator.EvalCtx.Empty with { Budget = budget };
        NeedCell? transported = null;
        var a = Runtime(budget, () =>
        {
            var identity = Evaluator.SupplyCell(new Expr.Param("leaf"), ctx.WithNeedEnv([("leaf", leaf)]), []).ProjectCallable();
            return identity.IsError ? identity.Error : transported!.ProjectCallable();
        }, span: SpanA);
        transported = a;
        for (var hop = 0; hop < 100; hop++)
            transported = Evaluator.SupplyCell(new Expr.Param("x"), ctx.WithNeedEnv([("x", transported)]), []);
        Assert.Same(a, transported);
        Assert.Equal(SpanA, Assert.IsType<EvalError.DemandCycle>(transported.ProjectCallable().Error).Span);
        Assert.Equal(1, a.ProjectionComputations);
        Assert.Equal(1, leafProjections);
        Assert.False(leaf.HasRuntimeProjection);
        Assert.Equal(0, leaf.ProjectionComputations);
        Assert.Equal(0, a.ProjectionActiveDependencyCount);
    }

    [Fact]
    public void SharedDependencyDiamond_HasNoFalseCycle_AndComputesTheSharedNodeOnce()
    {
        // A → B, A → C, B → D, C → D, D → V(receiver).
        var budget = EvaluationBudget.Create(null);
        var count = new Algorithm.Builtin(BuiltinId.@count);
        var receiverEvaluations = 0;
        var receiver = ValueCell(budget, () => { receiverEvaluations++; return Value(); });
        var d = Runtime(budget, () => AsCallable(receiver.Demand(), count));
        var b = Runtime(budget, () => d.ProjectCallable());
        var c = Runtime(budget, () => d.ProjectCallable());
        var a = Runtime(budget, () =>
        {
            var left = b.ProjectCallable();
            if (left.IsError) return left.Error;
            var right = c.ProjectCallable();
            return right.IsError ? right.Error : ReferenceEquals(left.Value, right.Value) ? left : new EvalError.TypeMismatch("identities differ");
        });
        Assert.Same(count, a.ProjectCallable().Value);
        Assert.Equal(1, d.ProjectionComputations);
        Assert.Equal(1, receiverEvaluations);
        Assert.All(new[] { a, b, c, d }, cell => Assert.Equal(0, cell.ProjectionActiveDependencyCount));
    }

    [Fact]
    public void DeepNoncyclicChains_CompleteOrStopAtTheStackGuard()
    {
        var count = new Algorithm.Builtin(BuiltinId.@count);
        EvalResult<Algorithm?> shallow = default, deep = default;
        EvaluationBudget shallowBudget = EvaluationBudget.Create(null), deepBudget = EvaluationBudget.Create(null);
        NeedCell[] Chain(EvaluationBudget budget, int length)
        {
            var cells = new NeedCell[length];
            cells[^1] = Runtime(budget, () => Identity(count));
            for (var i = length - 2; i >= 0; i--)
            {
                var next = i + 1;
                cells[i] = Runtime(budget, () => cells[next].ProjectCallable());
            }
            return cells;
        }
        var shallowCells = Chain(shallowBudget, 300);
        var deepCells = Chain(deepBudget, 200_000);
        AstStructuralDepthProcessTests.RunOnThreadWithStack(1024 * 1024, () =>
        {
            shallow = shallowCells[0].ProjectCallable();
            deep = deepCells[0].ProjectCallable();
        }, WaitLimit);
        Assert.Same(count, shallow.Value);
        Assert.All(shallowCells, cell => Assert.Equal(1, cell.ProjectionComputations));
        Assert.Null(shallowBudget.CheckContinuation());
        // The noncyclic chain is far deeper than the host stack: a resource limit, retained by the run.
        var limit = Assert.IsType<EvalError.EvaluationStackExhausted>(deep.Error);
        Assert.Same(limit, deepBudget.CheckContinuation());
        Assert.All(deepCells, cell => Assert.Equal(0, cell.ProjectionActiveDependencyCount));
        Assert.Equal(0, deepCells[^1].ProjectionComputations);
    }

    // ── Single flight under controlled overlap ───────────────────────────────────────────────

    public enum Outcome { Identity, Absence, OrdinaryFailure, ResourceLimit, Cancellation, HostException, Cycle }

    private sealed record Observed(EvalResult<Algorithm?>? Result, Exception? Exception);

    private static async Task<Observed> Observe(Func<ValueTask<EvalResult<Algorithm?>>> operation)
    {
        try { return new(await operation(), null); }
        catch (Exception error) { return new(null, error); }
    }

    [Theory]
    [InlineData(Outcome.Identity, false, false)]
    [InlineData(Outcome.Identity, true, true)]
    [InlineData(Outcome.Identity, true, false)]
    [InlineData(Outcome.Identity, false, true)]
    [InlineData(Outcome.Absence, false, false)]
    [InlineData(Outcome.Absence, true, true)]
    [InlineData(Outcome.OrdinaryFailure, false, false)]
    [InlineData(Outcome.OrdinaryFailure, true, true)]
    [InlineData(Outcome.OrdinaryFailure, false, true)]
    [InlineData(Outcome.ResourceLimit, false, false)]
    [InlineData(Outcome.ResourceLimit, true, true)]
    [InlineData(Outcome.Cancellation, false, false)]
    [InlineData(Outcome.Cancellation, true, true)]
    [InlineData(Outcome.Cancellation, true, false)]
    [InlineData(Outcome.HostException, false, false)]
    [InlineData(Outcome.HostException, true, true)]
    [InlineData(Outcome.HostException, false, true)]
    [InlineData(Outcome.Cycle, false, false)]
    [InlineData(Outcome.Cycle, true, true)]
    [InlineData(Outcome.Cycle, true, false)]
    public async Task IndependentObserverJoinsTheOneComputation_AndSharesItsOutcome(
        Outcome outcome, bool asynchronousStarter, bool asynchronousJoiner)
    {
        using var stop = new CancellationTokenSource();
        var budget = EvaluationBudget.Create(null, cancellationToken: stop.Token);
        var count = new Algorithm.Builtin(BuiltinId.@count);
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var cancellation = new OperationCanceledException("original cancellation", stop.Token);
        var host = new InvalidOperationException("original host exception");
        EvalError failure = new EvalError.IllegalInEval("original failure") { Span = SpanB };
        EvalError limit = new EvalError.EvaluationStepLimitExceeded(7) { Span = SpanB };
        var attempts = 0;
        NeedCell? cell = null;
        EvalResult<Algorithm?> Finish() => outcome switch
        {
            Outcome.Identity => Identity(count),
            Outcome.Absence => EvalResult<Algorithm?>.Ok(null),
            Outcome.OrdinaryFailure => failure,
            Outcome.ResourceLimit => limit,
            Outcome.Cancellation => Cancel(),
            Outcome.HostException => throw host,
            _ => throw new InvalidOperationException(),
        };
        EvalResult<Algorithm?> Cancel() { stop.Cancel(); throw cancellation; }
        cell = Runtime(budget, () =>
        {
            Interlocked.Increment(ref attempts);
            entered.SetResult();
            release.Task.Wait(WaitLimit);
            // The re-entry in the computation's own flow is a cycle; the computation publishes it.
            return outcome == Outcome.Cycle ? cell!.ProjectCallable() : Finish();
        }, async () =>
        {
            Interlocked.Increment(ref attempts);
            entered.SetResult();
            await release.Task.WaitAsync(WaitLimit);
            return outcome == Outcome.Cycle ? await cell!.ProjectCallableAsync() : Finish();
        }, SpanA, stop.Token);

        var starter = Task.Run(() => Observe(() => asynchronousStarter ? cell.ProjectCallableAsync() : new(cell.ProjectCallable())));
        await entered.Task.WaitAsync(WaitLimit);
        Assert.True(cell.HasProjectionInFlight);

        // The independent observer is the VALUE computation of another cell of the run, so its
        // wait-for edge to the projection node is observable before the computation is released.
        Observed? joined = null;
        EvalResult<Evaluator.CountedResult> Record(Observed observation)
        {
            joined = observation;
            if (observation.Exception is { } error) ExceptionDispatchInfo.Capture(error).Throw();
            return observation.Result!.Value.IsError ? observation.Result.Value.Error : Value();
        }
        var parent = ValueCell(budget,
            () => Record(Observe(() => new(cell.ProjectCallable())).GetAwaiter().GetResult()),
            async () => Record(await Observe(() => cell.ProjectCallableAsync())));
        var waiter = Task.Run(async () =>
        {
            try { if (asynchronousJoiner) await parent.DemandAsync(); else parent.Demand(); }
            catch (Exception) when (joined is not null) { }
        });
        await Until(() => parent.ActiveDependencyCount == 1 || waiter.IsCompleted);
        Assert.False(waiter.IsCompleted);
        Assert.Equal(1, parent.ActiveDependencyCount);
        Assert.Equal(1, Volatile.Read(ref attempts));
        Assert.False(cell.HasCallableMemo);

        release.SetResult();
        var first = await starter.WaitAsync(WaitLimit);
        await waiter.WaitAsync(WaitLimit);
        Assert.NotNull(joined);
        Assert.Equal(1, Volatile.Read(ref attempts));
        Assert.Equal(1, cell.ProjectionComputations);
        Assert.False(cell.HasProjectionInFlight);
        Assert.Equal(0, parent.ActiveDependencyCount);
        Assert.Equal(0, cell.ProjectionActiveDependencyCount);
        Assert.False(cell.HasCompletedValue);

        switch (outcome)
        {
            case Outcome.Cancellation:
            case Outcome.HostException:
                Exception expected = outcome == Outcome.Cancellation ? cancellation : host;
                Assert.Same(expected, first.Exception);
                Assert.Same(expected, joined!.Exception);
                Assert.False(cell.HasCallableMemo);
                var later = await Observe(() => cell.ProjectCallableAsync());
                if (outcome == Outcome.HostException) Assert.Same(host, later.Exception);
                else Assert.Equal(stop.Token, Assert.IsAssignableFrom<OperationCanceledException>(later.Exception).CancellationToken);
                break;
            default:
                Assert.Null(first.Exception);
                Assert.Null(joined!.Exception);
                var result = first.Result!.Value;
                Assert.Equal(result, joined.Result!.Value);
                if (outcome == Outcome.Identity) Assert.Same(count, joined.Result.Value.Value);
                if (outcome == Outcome.Absence) Assert.Null(joined.Result.Value.Value);
                if (outcome == Outcome.OrdinaryFailure)
                {
                    // META-S3-0b provenance: the published outcome is the computation's failure
                    // marked as a runtime projection failure (an equality-transparent copy), the
                    // SAME object for every observer.
                    Assert.Equal(failure, joined.Result.Value.Error);
                    Assert.True(joined.Result.Value.Error.IsProjectionFailure);
                    Assert.Same(first.Result.Value.Error, joined.Result.Value.Error);
                }
                if (outcome == Outcome.ResourceLimit)
                {
                    Assert.Same(limit, joined.Result.Value.Error);
                    Assert.Same(limit, budget.CheckContinuation());
                }
                if (outcome == Outcome.Cycle)
                    Assert.Equal(SpanA, Assert.IsType<EvalError.DemandCycle>(joined.Result.Value.Error).Span);
                Assert.True(cell.HasCallableMemo);
                // A later observation reuses the completed outcome; a cell's own limit keeps its provenance.
                Assert.Equal(result, cell.ProjectCallable());
                Assert.Equal(result, await cell.ProjectCallableAsync());
                break;
        }
        Assert.Equal(1, cell.ProjectionComputations);
        Assert.False(NeedNode.HasCurrentNode);
    }

    [Fact]
    public async Task ManyOverlappingObservers_StartOneComputation()
    {
        var budget = EvaluationBudget.Create(null);
        var count = new Algorithm.Builtin(BuiltinId.@count);
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var attempts = 0;
        var cell = Runtime(budget, () => throw new InvalidOperationException("sync computation"), async () =>
        {
            Interlocked.Increment(ref attempts);
            entered.TrySetResult();
            await release.Task;
            return Identity(count);
        });
        var parents = Enumerable.Range(0, 32).Select(_ => ValueCell(budget, () => throw new InvalidOperationException(),
            async () => (await cell.ProjectCallableAsync()).IsOk ? Value() : new EvalError.TypeMismatch("lost"))).ToArray();
        var demands = parents.Select(parent => Task.Run(async () => await parent.DemandAsync())).ToArray();
        await entered.Task.WaitAsync(WaitLimit);
        await Until(() => parents.All(parent => parent.ActiveDependencyCount == 1));
        Assert.Equal(1, Volatile.Read(ref attempts));
        release.SetResult();
        var values = await Task.WhenAll(demands).WaitAsync(WaitLimit);
        Assert.All(values, value => Assert.True(value.IsOk));
        Assert.Equal(1, cell.ProjectionComputations);
        Assert.Same(count, cell.ProjectCallable().Value);
        Assert.All(parents, parent => Assert.Equal(0, parent.ActiveDependencyCount));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task IndependentFlowsClosingAWaitCycle_AreBothDemandCycle(bool throughValue)
    {
        // Flow 1 computes C(A), which waits on B; flow 2 computes C(B), which waits on A — on its
        // CALLABLE (C/C) or on its VALUE (V/C) — after flow 1's edge exists.
        var budget = EvaluationBudget.Create(null);
        var count = new Algorithm.Builtin(BuiltinId.@count);
        var enteredA = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var enteredB = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var releaseA = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var releaseB = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        NeedCell? a = null, b = null;
        async ValueTask<EvalResult<Algorithm?>> ProjectAAsync()
        {
            enteredA.SetResult();
            await releaseA.Task;
            return await b!.ProjectCallableAsync();
        }
        a = NeedCell.WithRuntimeProjection(() => Value(),
            async () => { var projected = await ProjectAAsync(); return projected.IsError ? projected.Error : Value(); },
            () => throw new InvalidOperationException(), ProjectAAsync, SpanA, budget);
        b = Runtime(budget, () => throw new InvalidOperationException(), async () =>
        {
            enteredB.SetResult();
            await releaseB.Task;
            return throughValue ? AsCallable(await a.DemandAsync(), count) : await a.ProjectCallableAsync();
        }, SpanB);
        var first = Task.Run(async () => throughValue ? AsCallable(await a.DemandAsync(), count) : await a.ProjectCallableAsync());
        var second = Task.Run(async () => await b.ProjectCallableAsync());
        await Task.WhenAll(enteredA.Task, enteredB.Task).WaitAsync(WaitLimit);
        releaseA.SetResult();
        await Until(() => (throughValue ? a.ActiveDependencyCount : a.ProjectionActiveDependencyCount) == 1);
        releaseB.SetResult();
        var results = await Task.WhenAll(first, second).WaitAsync(WaitLimit);
        Assert.All(results, result => Assert.Equal(KatLangErrorCode.DemandCycle, result.Error.Code));
        Assert.Equal(0, a.ActiveDependencyCount);
        Assert.Equal(0, a.ProjectionActiveDependencyCount);
        Assert.Equal(0, b.ProjectionActiveDependencyCount);
        Assert.Equal(1, b.ProjectionComputations);
    }

    [Fact]
    public async Task IndependentOverlappingDependencies_ShareOneComputationWithoutAFalseCycle()
    {
        // Two flows project different runtime cells (one through a VALUE cell) that both wait on
        // one held runtime projection D: both join D, nothing is cyclic.
        var budget = EvaluationBudget.Create(null);
        var count = new Algorithm.Builtin(BuiltinId.@count);
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var d = Runtime(budget, () => throw new InvalidOperationException(), async () =>
        {
            entered.TrySetResult();
            await release.Task;
            return Identity(count);
        });
        var left = Runtime(budget, () => throw new InvalidOperationException(), () => d.ProjectCallableAsync());
        var middle = ValueCell(budget, () => throw new InvalidOperationException(),
            async () => (await d.ProjectCallableAsync()).IsOk ? Value() : new EvalError.TypeMismatch("lost"));
        var right = Runtime(budget, () => throw new InvalidOperationException(), async () => AsCallable(await middle.DemandAsync(), count));
        var first = Task.Run(async () => await left.ProjectCallableAsync());
        await entered.Task.WaitAsync(WaitLimit);
        var second = Task.Run(async () => await right.ProjectCallableAsync());
        await Until(() => middle.ActiveDependencyCount == 1 && left.ProjectionActiveDependencyCount == 1);
        release.SetResult();
        var results = await Task.WhenAll(first, second).WaitAsync(WaitLimit);
        Assert.All(results, result => Assert.Same(count, result.Value));
        Assert.Equal(1, d.ProjectionComputations);
        Assert.All(new[] { left, right, d }, cell => Assert.Equal(0, cell.ProjectionActiveDependencyCount));
        Assert.Equal(0, middle.ActiveDependencyCount);
    }

    // ── Terminality and cancellation at observation entry ────────────────────────────────────

    [Fact]
    public async Task TerminalRunAnswersBeforeAMemoizedIdentity_AndStartsNoProjection()
    {
        var budget = EvaluationBudget.Create(null);
        var count = new Algorithm.Builtin(BuiltinId.@count);
        var memoized = Runtime(budget, () => Identity(count));
        var identityOnly = new NeedCell(() => Value(), () => new(Value()), () => Identity(count), budget: budget);
        Assert.Same(count, memoized.ProjectCallable().Value);
        Assert.Same(count, identityOnly.ProjectCallable().Value);
        var terminal = budget.RetainTerminal(new EvalError.EvaluationStepLimitExceeded(3));
        Assert.Same(terminal, memoized.ProjectCallable().Error);
        Assert.Same(terminal, (await memoized.ProjectCallableAsync()).Error);
        Assert.Same(terminal, identityOnly.ProjectCallable().Error);
        var attempts = 0;
        var fresh = Runtime(budget, () => { attempts++; return Identity(count); });
        Assert.Same(terminal, fresh.ProjectCallable().Error);
        Assert.Equal(0, attempts);
        Assert.Equal(0, fresh.ProjectionComputations);
        Assert.False(fresh.HasCallableMemo);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task ObservationAdmittedBeforeIndependentTerminality_ReceivesItsCompletion(bool callable)
    {
        // The observation-entry contract, VALUE and CALLABLE alike: an admitted flight completes
        // normally; every NEW observation then answers with the terminal run before the memo.
        var budget = EvaluationBudget.Create(null);
        var count = new Algorithm.Builtin(BuiltinId.@count);
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var cell = NeedCell.WithRuntimeProjection(() => Value(),
            async () => { entered.SetResult(); await release.Task; return Value(); },
            () => Identity(count),
            async () => { entered.SetResult(); await release.Task; return Identity(count); }, budget: budget);
        var first = Task.Run(async () => callable ? (await cell.ProjectCallableAsync()).IsOk : (await cell.DemandAsync()).IsOk);
        await entered.Task.WaitAsync(WaitLimit);
        var terminal = budget.RetainTerminal(new EvalError.EvaluationStepLimitExceeded(9));
        release.SetResult();
        Assert.True(await first.WaitAsync(WaitLimit));
        Assert.Same(terminal, callable ? (await cell.ProjectCallableAsync()).Error : (await cell.DemandAsync()).Error);
        Assert.Equal(callable, cell.HasCallableMemo);
        Assert.Equal(!callable, cell.HasCompletedValue);
    }

    [Fact]
    public async Task CancellationAfterAnAdmittedWait_KeepsTheCompletionAndRejectsLaterWork()
    {
        using var stop = new CancellationTokenSource();
        var budget = EvaluationBudget.Create(null, cancellationToken: stop.Token);
        var count = new Algorithm.Builtin(BuiltinId.@count);
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var release = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var cell = Runtime(budget, () => throw new InvalidOperationException(),
            async () => { entered.SetResult(); await release.Task; return Identity(count); }, token: stop.Token);
        var parent = ValueCell(budget, () => throw new InvalidOperationException(),
            async () => (await cell.ProjectCallableAsync()).IsOk ? Value() : new EvalError.TypeMismatch("lost"));
        var starter = Task.Run(async () => await cell.ProjectCallableAsync());
        await entered.Task.WaitAsync(WaitLimit);
        var waiter = Task.Run(async () => await parent.DemandAsync());
        await Until(() => parent.ActiveDependencyCount == 1);
        stop.Cancel();
        release.SetResult();
        Assert.Same(count, (await starter.WaitAsync(WaitLimit)).Value);
        Assert.True((await waiter.WaitAsync(WaitLimit)).IsOk);
        Assert.True(cell.HasCallableMemo);
        var later = Assert.ThrowsAny<OperationCanceledException>(() => cell.ProjectCallable());
        Assert.Equal(stop.Token, later.CancellationToken);
        Assert.Equal(1, cell.ProjectionComputations);
        Assert.Equal(0, parent.ActiveDependencyCount);
    }

    [Fact]
    public async Task CancelledValueChannel_IsObservedByTheCallableChannel()
    {
        // NEED-09 cancellation belongs to the run: a cell whose VALUE was cancelled by a host
        // cancellation (no run token) rethrows it on the CALLABLE channel too, as before.
        var budget = EvaluationBudget.Create(null);
        var cancelled = new OperationCanceledException("host cancelled");
        var count = new Algorithm.Builtin(BuiltinId.@count);
        var cell = Runtime(budget, () => Identity(count), value: () => throw cancelled);
        Assert.Same(cancelled, Assert.Throws<OperationCanceledException>(() => cell.Demand()));
        Assert.Same(cancelled, Assert.Throws<OperationCanceledException>(() => cell.ProjectCallable()));
        Assert.Same(cancelled, await Assert.ThrowsAsync<OperationCanceledException>(() => cell.ProjectCallableAsync().AsTask()));
        Assert.Equal(0, cell.ProjectionComputations);
    }

    [Fact]
    public void CancellationInsideTheComputation_IsStoredNotPublished_AndNeverRestarts()
    {
        using var stop = new CancellationTokenSource();
        var budget = EvaluationBudget.Create(null, cancellationToken: stop.Token);
        var receiver = new NeedCell(() => { stop.Cancel(); stop.Token.ThrowIfCancellationRequested(); return Value(); },
            () => new(Value()), budget: budget, token: stop.Token);
        var count = new Algorithm.Builtin(BuiltinId.@count);
        var cell = Runtime(budget, () => AsCallable(receiver.Demand(), count), token: stop.Token);
        var thrown = Assert.ThrowsAny<OperationCanceledException>(() => cell.ProjectCallable());
        Assert.Equal(stop.Token, thrown.CancellationToken);
        Assert.False(cell.HasCallableMemo);
        Assert.Equal(0, cell.ProjectionActiveDependencyCount);
        Assert.Equal(0, receiver.ActiveDependencyCount);
        Assert.ThrowsAny<OperationCanceledException>(() => cell.ProjectCallable());
        Assert.Equal(1, cell.ProjectionComputations);
        Assert.False(NeedNode.HasCurrentNode);
    }

    // ── Channel independence and the identity-only path ──────────────────────────────────────

    [Fact]
    public async Task ChannelsAreIndependent_NeitherComputesTheOther()
    {
        var budget = EvaluationBudget.Create(null);
        var count = new Algorithm.Builtin(BuiltinId.@count);
        var evaluations = 0;
        var cell = Runtime(budget, () => Identity(count), value: () => { evaluations++; return Value(); });
        Assert.Same(count, cell.ProjectCallable().Value);
        Assert.Equal(0, evaluations);
        Assert.False(cell.HasCompletedValue);
        Assert.True(cell.Demand().IsOk);
        Assert.True((await cell.DemandAsync()).IsOk);
        Assert.Equal(1, evaluations);
        Assert.Equal(1, cell.ProjectionComputations);

        var valueFirst = Runtime(budget, () => Identity(count), value: () => Value(5));
        Assert.True(valueFirst.Demand().IsOk);
        Assert.Equal(0, valueFirst.ProjectionComputations);
        Assert.False(valueFirst.HasCallableMemo);
    }

    [Fact]
    public async Task IdentityOnlyProjection_HasNoNodeOrFlight_AndRereadsAllocateNothing()
    {
        var budget = EvaluationBudget.Create(null);
        var count = new Algorithm.Builtin(BuiltinId.@count);
        var projections = 0;
        var hostBuilt = new NeedCell(() => Value(), () => new(Value()), () => { projections++; return Identity(count); }, budget: budget);
        var written = Evaluator.SupplyCell(new Expr.Num(5), Evaluator.EvalCtx.Empty with { Budget = budget }, []);
        Assert.Same(count, hostBuilt.ProjectCallable().Value);
        Assert.True(written.ProjectCallable().IsOk);
        // Warm the paths, then measure memo re-reads on this thread.
        for (var i = 0; i < 16; i++) { hostBuilt.ProjectCallable(); written.ProjectCallable(); _ = hostBuilt.ProjectCallableAsync(); }
        var before = GC.GetAllocatedBytesForCurrentThread();
        for (var i = 0; i < 1_000; i++)
        {
            hostBuilt.ProjectCallable();
            written.ProjectCallable();
            // A memo re-read completes synchronously, so the await never leaves the measured thread.
            var reread = hostBuilt.ProjectCallableAsync();
            Assert.True(reread.IsCompletedSuccessfully);
            _ = await reread;
        }
        Assert.Equal(0, GC.GetAllocatedBytesForCurrentThread() - before);
        Assert.Equal(1, projections);
        Assert.All(new[] { hostBuilt, written }, cell =>
        {
            Assert.False(cell.HasRuntimeProjection);
            Assert.False(cell.HasProjectionInFlight);
            Assert.Equal(0, cell.ProjectionComputations);
            Assert.Equal(0, cell.ProjectionActiveDependencyCount);
        });
    }

    [Fact]
    public void OrdinaryCells_CarryNoCallableFlightState()
    {
        // The CALLABLE flight lives on the lazily held projection node, never on every cell: the
        // cell hierarchy keeps exactly the VALUE flight's completion and stored exception.
        var fields = new List<FieldInfo>();
        for (var type = typeof(NeedCell); type is not null && type != typeof(object); type = type.BaseType)
            fields.AddRange(type.GetFields(BindingFlags.Instance | BindingFlags.NonPublic | BindingFlags.Public | BindingFlags.DeclaredOnly));
        Assert.Single(fields, field => field.FieldType.IsGenericType
            && field.FieldType.GetGenericTypeDefinition() == typeof(TaskCompletionSource<>));
        Assert.Single(fields, field => field.FieldType == typeof(ExceptionDispatchInfo));
        Assert.DoesNotContain(fields, field => field.FieldType.Name == "ProjectionNode");
        Assert.Equal(16, fields.Count);
    }
}
