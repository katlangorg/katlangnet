using System.Diagnostics;
using System.Numerics;
using System.Reflection;
using KatLang.Evaluation;
using KatLang.Optimizations.Loops;

namespace KatLang.Tests;

/// <summary>
/// META-S3-0b — non-initiating observation, the ONE asynchronous resolution adapter
/// (<c>Evaluator.ResolveAsync</c>) with VALUE and CALLABLE outcome replay, its progress guards,
/// the async CALLABLE consumers (callee, dot receiver, lexical fallback, <c>.string</c> member,
/// sequence callbacks, loop steps, repeated-name binder) and runtime-projection failure
/// provenance. No source program builds a runtime projection before META-S3-1, so every case
/// drives the production machinery through the internal construction point
/// <see cref="NeedCell.WithRuntimeProjection"/>: either directly (the resolver units) or bound as
/// a parameter cell under a host-built AST evaluated by the production sync engine and its
/// async twin. Sync/async agreement compares the full structured error (kind, payload, span and
/// context chain), the result value, the run's step charges and the computation counts.
/// </summary>
public sealed class NeedCellAsyncResolutionTests
{
    private static readonly TimeSpan WaitLimit = TimeSpan.FromSeconds(30);
    private static readonly SourceSpan SpanU = new(2, 3, 2, 4);
    private static readonly SourceSpan SpanA = new(3, 3, 3, 4);
    private static readonly SourceSpan SpanB = new(4, 3, 4, 4);

    private static readonly EvalResult<Evaluator.CountedResult> One = Value(1);

    private static EvalResult<Evaluator.CountedResult> Value(int number)
        => EvalResult<Evaluator.CountedResult>.Ok(new(new Result.Atom((Decimal128)number), 1));

    private static readonly Algorithm.Builtin Count = new(BuiltinId.@count);

    // I(x) = x — the callable most projections below yield.
    private static readonly Algorithm.User IdentityAlgorithm =
        new(null, [new CaptureParameterPattern("x")], [], [], [new Expr.Param("x")]);

    private static EvalResult<Algorithm?> Identity() => EvalResult<Algorithm?>.Ok(IdentityAlgorithm);

    private static EvaluationBudget NewBudget(bool asynchronous = false, CancellationToken token = default, EvaluationLimits? limits = null)
    {
        var budget = EvaluationBudget.Create(limits, cancellationToken: token);
        // These programs are evaluated below the preflight; a loop builtin binds a META parameter
        // (META-S3-3), so record the run's J7 decision the program gate would make.
        budget.DecideInvocationPlanRetention(programMayCapture: true);
        if (asynchronous) budget.MarkAsynchronousRun();
        return budget;
    }

    private static Evaluator.EvalCtx Ctx(EvaluationBudget budget, params (string Name, NeedCell Cell)[] needs)
        => (Evaluator.EvalCtx.Empty with
            {
                Budget = budget,
                EnableLoopOptimization = false,
                EnableSequencePipelineOptimization = false,
                // Async-capable (the async twin requires it); the sync engine uses its sync member.
                ZeroArgPropertyResultCache = new KatLang.Evaluation.Caching.RunScopedAsyncZeroArgPropertyResultCache(),
            })
            .WithNeedEnv(needs);

    private static NeedCell Runtime(EvaluationBudget budget, Func<EvalResult<Algorithm?>> project,
        Func<ValueTask<EvalResult<Algorithm?>>>? projectAsync = null, SourceSpan? span = null,
        CancellationToken token = default)
        => NeedCell.WithRuntimeProjection(() => One, () => new(One), project, projectAsync ?? (() => new(project())),
            span, budget, token);

    private static NeedCell ValueCell(EvaluationBudget budget, Func<EvalResult<Evaluator.CountedResult>> evaluate,
        Func<ValueTask<EvalResult<Evaluator.CountedResult>>>? evaluateAsync = null, SourceSpan? span = null,
        CancellationToken token = default)
        => new(evaluate, evaluateAsync ?? (() => new(evaluate())), span: span, budget: budget, token: token);

    private static EvalResult<T> ThenIdentity<T>(EvalResult<Evaluator.CountedResult> value, EvalResult<T> identity)
        => value.IsError ? value.Error : identity;

    private static ValueTask<EvalResult<T>> ResolveAsync<T>(EvaluationBudget budget, Func<EvalResult<T>> resolve)
        => Evaluator.ResolveAsync(Ctx(budget), resolve, static r => r());

    private static readonly MethodInfo EvalCountedAsyncMethod = typeof(Evaluator).GetMethod("EvalCountedAsync",
        BindingFlags.Static | BindingFlags.NonPublic,
        [typeof(Expr), typeof(Evaluator.EvalCtx), typeof(IReadOnlyList<(string Name, Result Value)>)])!;

    private static async Task<EvalResult<Evaluator.CountedResult>> EvalAsync(Expr program, Evaluator.EvalCtx ctx)
        => await ((ValueTask<EvalResult<Evaluator.CountedResult>>)EvalCountedAsyncMethod.Invoke(null,
            [program, ctx, Array.Empty<(string, Result)>()])!).AsTask().WaitAsync(WaitLimit);

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context) error = context.Inner;
        return error;
    }

    private static string Show(EvalResult<Evaluator.CountedResult> result)
        => result.IsOk ? "ok " + SixRouteAgreement.Neutral(result.Value.Value) : "err " + result.Error;

    // ── Non-initiating observation ──────────────────────────────────────────────────────────

    [Fact]
    public void Observation_NeverStartsAValueOrARuntimeProjection_AndReportsTheFirstPendingPair()
    {
        var budget = NewBudget();
        var evaluations = 0;
        var projections = 0;
        var value = ValueCell(budget, () => { evaluations++; return One; });
        var runtime = Runtime(budget, () => { projections++; return Identity(); });
        var scope = NeedCell.EnterObservation();
        try
        {
            Assert.True(NeedCell.IsObservationPending(value.Demand().Error));
            Assert.True(NeedCell.IsObservationPending(runtime.ProjectCallable().Error));
            Assert.Same(value, scope.Pending);
            Assert.Equal(NeedCell.Channel.Value, scope.PendingChannel);
        }
        finally { NeedCell.ExitObservation(scope); }
        Assert.False(NeedCell.IsObserving);
        Assert.Equal(0, evaluations);
        Assert.Equal(0, projections);
        Assert.Equal(0, runtime.ProjectionComputations);
        Assert.False(value.HasCompletedValue);
        Assert.False(runtime.HasCallableMemo);
        Assert.False(runtime.HasProjectionInFlight);
        Assert.Equal(0, value.ActiveDependencyCount);
        Assert.False(NeedNode.HasCurrentNode);
        Assert.Equal(0, budget.ConsumedSteps);
    }

    [Fact]
    public void Observation_ReadsCompletedMemosAndIdentityOnlyFacts_WithoutReportingPending()
    {
        var budget = NewBudget();
        var value = ValueCell(budget, () => One);
        var runtime = Runtime(budget, Identity);
        Assert.True(value.Demand().IsOk);
        Assert.Same(IdentityAlgorithm, runtime.ProjectCallable().Value);
        var identityOnly = new NeedCell(() => One, () => new(One), () => EvalResult<Algorithm?>.Ok(Count), budget: budget);
        var scope = NeedCell.EnterObservation();
        try
        {
            Assert.Equal(One, value.Demand());
            Assert.Same(IdentityAlgorithm, runtime.ProjectCallable().Value);
            Assert.Same(Count, identityOnly.ProjectCallable().Value);
            Assert.Null(scope.Pending);
        }
        finally { NeedCell.ExitObservation(scope); }
        // Published under the observation: no pending pair tainted it.
        Assert.True(identityOnly.HasCallableMemo);
        Assert.Equal(1, runtime.ProjectionComputations);
    }

    [Fact]
    public void Observation_Order_IsTerminalThenMemoThenRecordThenPending()
    {
        var budget = NewBudget();
        var memoized = ValueCell(budget, () => Value(7));
        Assert.Equal(Value(7), memoized.Demand());
        var recordedOnly = ValueCell(budget, () => Value(8));
        var projected = Runtime(budget, Identity);
        Assert.True(projected.ProjectCallable().IsOk);
        var unprojected = Runtime(budget, Identity);
        var record = new NeedCell.ResolutionRecord();
        record.RecordValue(memoized, Value(99));          // a memo wins over a record
        record.RecordValue(recordedOnly, Value(5));
        record.RecordCallable(projected, EvalResult<Algorithm?>.Ok(Count));
        record.RecordCallable(unprojected, EvalResult<Algorithm?>.Ok(Count));
        var scope = NeedCell.EnterObservation(record);
        try
        {
            Assert.Equal(Value(7), memoized.Demand());
            Assert.Equal(Value(5), recordedOnly.Demand());
            Assert.Same(IdentityAlgorithm, projected.ProjectCallable().Value);
            Assert.Same(Count, unprojected.ProjectCallable().Value);
            Assert.Null(scope.Pending);
            // Terminality answers before the memo and before the record.
            var limit = budget.RetainTerminal(new EvalError.EvaluationStepLimitExceeded(3));
            Assert.Same(limit, memoized.Demand().Error);
            Assert.Same(limit, recordedOnly.Demand().Error);
            Assert.Same(limit, projected.ProjectCallable().Error);
            Assert.Same(limit, unprojected.ProjectCallable().Error);
            Assert.Null(scope.Pending);
        }
        finally { NeedCell.ExitObservation(scope); }
        Assert.False(recordedOnly.HasCompletedValue);
        Assert.Equal(0, unprojected.ProjectionComputations);
        Assert.False(unprojected.HasCallableMemo);
    }

    [Fact]
    public void Observation_PropagatesCancellation_AndAlwaysExitsItsScope()
    {
        using var stop = new CancellationTokenSource();
        var budget = NewBudget(token: stop.Token);
        var value = ValueCell(budget, () => One, token: stop.Token);
        stop.Cancel();
        var scope = NeedCell.EnterObservation();
        try { Assert.Throws<OperationCanceledException>(() => value.Demand()); }
        finally { NeedCell.ExitObservation(scope); }
        Assert.False(NeedCell.IsObserving);
        Assert.Null(scope.Pending);
    }

    [Fact]
    public void NestedObservation_DoesNotSeeTheOuterResolutionsRecord()
    {
        var budget = NewBudget();
        var cell = ValueCell(budget, () => One);
        var record = new NeedCell.ResolutionRecord();
        record.RecordValue(cell, Value(4));
        var outer = NeedCell.EnterObservation(record);
        try
        {
            var inner = NeedCell.EnterObservation();
            try
            {
                Assert.True(NeedCell.IsObservationPending(cell.Demand().Error));
                Assert.Same(cell, inner.Pending);
            }
            finally { NeedCell.ExitObservation(inner); }
            Assert.Equal(Value(4), cell.Demand());
            Assert.Null(outer.Pending);
        }
        finally { NeedCell.ExitObservation(outer); }
        Assert.Throws<UnreachableException>(() => NeedCell.ExitObservation(outer));
    }

    [Fact]
    public void IdentityOnlyProjection_ReachingAPendingRuntimeProjection_IsNotPublished()
    {
        var budget = NewBudget();
        var runtime = Runtime(budget, Identity);
        // An identity-only (host-built) projection that reaches the pending runtime projection reports
        // it pending and publishes nothing of its own.
        var identityOnly = new NeedCell(() => One, () => new(One), runtime.ProjectCallable, budget: budget);
        Assert.False(identityOnly.HasRuntimeProjection);
        var scope = NeedCell.EnterObservation();
        try { Assert.True(NeedCell.IsObservationPending(identityOnly.ProjectCallable().Error)); }
        finally { NeedCell.ExitObservation(scope); }
        Assert.Same(runtime, scope.Pending);
        Assert.Equal(NeedCell.Channel.Callable, scope.PendingChannel);
        Assert.False(identityOnly.HasCallableMemo);
        Assert.Equal(0, runtime.ProjectionComputations);
    }

    [Fact]
    public void AParameterRootedPath_InARunWithRuntimeProjections_IsItselfARuntimeProjection()
    {
        // META-S3-1 (the classification S3-0b left to S3-1): a supplied `p.G` whose head parameter can
        // be a runtime projection is a runtime projection node itself, so observing it reports THAT
        // cell pending and starts nothing — neither its own computation nor p's.
        var budget = NewBudget();
        var runtime = Runtime(budget, Identity);
        var ctx = Ctx(budget, ("p", runtime));
        var argument = Evaluator.SupplyCell(new Expr.DotCall(new Expr.Param("p"), "G"), ctx, []);
        Assert.True(argument.HasRuntimeProjection);
        var scope = NeedCell.EnterObservation();
        try { Assert.True(NeedCell.IsObservationPending(argument.ProjectCallable().Error)); }
        finally { NeedCell.ExitObservation(scope); }
        Assert.Same(argument, scope.Pending);
        Assert.Equal(NeedCell.Channel.Callable, scope.PendingChannel);
        Assert.False(argument.HasCallableMemo);
        Assert.Equal(0, argument.ProjectionComputations);
        Assert.Equal(0, runtime.ProjectionComputations);
        // Outside an observation the projection runs once, through p's runtime projection.
        Assert.True(argument.ProjectCallable().IsOk);
        Assert.Equal(1, argument.ProjectionComputations);
        Assert.Equal(1, runtime.ProjectionComputations);
    }

    [Fact]
    public void PeekCallable_IsNonInitiating()
    {
        var budget = NewBudget();
        var runtime = Runtime(budget, Identity);
        Assert.Null(runtime.PeekCallable());
        Assert.Equal(0, runtime.ProjectionComputations);
        Assert.Same(IdentityAlgorithm, runtime.ProjectCallable().Value);
        Assert.Same(IdentityAlgorithm, runtime.PeekCallable());
        var failed = Runtime(budget, () => new EvalError.IllegalInEval("boom"));
        Assert.True(failed.ProjectCallable().IsError);
        Assert.Null(failed.PeekCallable());
        // Without a runtime projection in the run the read is the ordinary projection.
        var plain = new NeedCell(() => One, () => new(One), () => EvalResult<Algorithm?>.Ok(Count), budget: NewBudget());
        Assert.Same(Count, plain.PeekCallable());
    }

    [Fact]
    public void PeekCallable_WithoutAnOwningBudget_DoesNotStartRuntimeProjection()
    {
        var computations = 0;
        var cell = NeedCell.WithRuntimeProjection(() => One, () => new(One),
            () => { computations++; return Identity(); }, () => new(Identity()));

        Assert.Null(cell.PeekCallable());
        Assert.Equal(0, computations);
        Assert.Equal(0, cell.ProjectionComputations);
        Assert.False(cell.HasCallableMemo);
        Assert.False(NeedCell.IsObserving);

        Assert.Same(IdentityAlgorithm, cell.ProjectCallable().Value);
        Assert.Same(IdentityAlgorithm, cell.PeekCallable());
        Assert.Equal(1, computations);
    }

    [Fact]
    public void PeekResolve_DeclinesInsteadOfInitiating()
    {
        var budget = NewBudget();
        var runtime = Runtime(budget, Identity);
        var ctx = Ctx(budget);
        Assert.Null(Evaluator.PeekResolve(ctx, runtime, static cell => cell.ProjectCallable()));
        Assert.Equal(0, runtime.ProjectionComputations);
        Assert.True(runtime.ProjectCallable().IsOk);
        Assert.Same(IdentityAlgorithm, Evaluator.PeekResolve(ctx, runtime, static cell => cell.ProjectCallable())!.Value.Value);
    }

    // ── The guards ──────────────────────────────────────────────────────────────────────────

    [Fact]
    public void GuardB_AFreshRuntimeProjectionAllocatedWhileObserving_FailsLoud()
    {
        var budget = NewBudget();
        var scope = NeedCell.EnterObservation();
        try { Assert.Throws<UnreachableException>(() => Runtime(budget, Identity)); }
        finally { NeedCell.ExitObservation(scope); }
        Assert.NotNull(Runtime(budget, Identity));
    }

    [Fact]
    public async Task GuardB_ThroughResolveAsync_FailsLoudRatherThanRetrying()
    {
        var budget = NewBudget(asynchronous: true);
        _ = Runtime(budget, Identity);   // the run has runtime projections: resolutions observe
        var attempts = 0;
        await Assert.ThrowsAsync<UnreachableException>(async () => await ResolveAsync(budget, () =>
        {
            attempts++;
            return Runtime(budget, Identity).ProjectCallable();   // a cell new at every retry
        }));
        Assert.Equal(1, attempts);
        Assert.False(NeedCell.IsObserving);
    }

    [Fact]
    public async Task GuardA_APairReportedPendingAfterItsOutcomeWasRecorded_FailsLoud()
    {
        var budget = NewBudget(asynchronous: true);
        var cell = ValueCell(budget, () => One, async () => { await Task.Yield(); return new EvalError.DemandCycle { Span = SpanU }; });
        _ = Runtime(budget, Identity);
        var attempts = 0;
        // A (hypothetical) route that ignores the resolution's record: the recorded VALUE pair is
        // reported pending again. The adapter must fail loud, never loop or invent an outcome.
        var error = await Assert.ThrowsAsync<UnreachableException>(async () => await ResolveAsync(budget, () =>
        {
            attempts++;
            var observed = cell.Demand();
            if (attempts > 1) NeedCell.CurrentObservation!.MarkPending(cell, NeedCell.Channel.Value);
            return observed;
        }));
        Assert.Contains("no progress", error.Message);
        Assert.Equal(2, attempts);
        Assert.Equal(1, budget.ResolutionRetries);
        Assert.False(NeedCell.IsObserving);
    }

    [Fact]
    public async Task AnUnpublishedRuntimeProjectionReachedSynchronouslyInAnAsyncRun_FailsLoud()
    {
        var budget = NewBudget(asynchronous: true);
        var runtime = Runtime(budget, Identity);
        Assert.Throws<UnreachableException>(() => runtime.ProjectCallable());
        Assert.Equal(0, runtime.ProjectionComputations);
        // The host-built program reaching it synchronously (the sync engine inside an async run).
        var program = new Expr.Call(new Expr.Param("f"), [new Expr.Num(3)]);
        Assert.Throws<UnreachableException>(() => Evaluator.EvalCounted(program, Ctx(budget, ("f", runtime)), []));
        // Once published (awaited), a synchronous read is a memo hit.
        Assert.Same(IdentityAlgorithm, (await runtime.ProjectCallableAsync()).Value);
        Assert.Same(IdentityAlgorithm, runtime.ProjectCallable().Value);
    }

    [Fact]
    public async Task AnAsynchronousStartInsideAnObservation_FailsLoud()
    {
        var budget = NewBudget();
        var value = ValueCell(budget, () => One);
        var runtime = Runtime(budget, Identity);
        var scope = NeedCell.EnterObservation();
        ValueTask<EvalResult<Evaluator.CountedResult>> demand;
        ValueTask<EvalResult<Algorithm?>> projection;
        try
        {
            demand = value.DemandAsync();
            projection = runtime.ProjectCallableAsync();
        }
        finally { NeedCell.ExitObservation(scope); }
        await Assert.ThrowsAsync<UnreachableException>(async () => await demand);
        await Assert.ThrowsAsync<UnreachableException>(async () => await projection);
        Assert.False(value.HasCompletedValue);
        Assert.Equal(0, runtime.ProjectionComputations);
    }

    // ── ResolveAsync: progress and outcome replay (R2 p-* units) ────────────────────────────

    [Fact]
    public async Task WithoutRuntimeProjections_TheResolverRunsOnceWithNoObservation()
    {
        var budget = NewBudget(asynchronous: true);
        var cell = new NeedCell(() => One, () => new(One), () => EvalResult<Algorithm?>.Ok(Count), budget: budget);
        var attempts = 0;
        var observing = true;
        var result = await ResolveAsync(budget, () => { attempts++; observing = NeedCell.IsObserving; return cell.ProjectCallable(); });
        Assert.Same(Count, result.Value);
        Assert.Equal(1, attempts);
        Assert.False(observing);
        Assert.Equal(0, budget.ResolutionRetries);
    }

    // THE crucial case: VALUE(U) → [async resolution: CALLABLE(L) → VALUE(U)]. The re-entry's
    // DemandCycle is flow-local and never memoized at U; it is recorded and replayed, so the
    // resolution terminates instead of retrying the unchanged pending U.
    [Fact]
    public async Task UnpublishedValueDemandCycle_IsReplayed_AndTerminatesWithoutRetryingThePendingCell()
    {
        var budget = NewBudget(asynchronous: true);
        NeedCell? u = null, l = null;
        var evaluations = 0;
        var attempts = 0;
        l = Runtime(budget, () => ThenIdentity(u!.Demand(), Identity()),
            () => ResolveAsync(budget, () => { attempts++; return ThenIdentity(u!.Demand(), Identity()); }), SpanA);
        u = ValueCell(budget, () => One, async () =>
        {
            evaluations++;
            await Task.Yield();
            var callee = await ResolveAsync(budget, () => l.ProjectCallable());
            return callee.IsError ? callee.Error : One;
        }, SpanU);

        var result = await u.DemandAsync().AsTask().WaitAsync(WaitLimit);

        var cycle = Assert.IsType<EvalError.DemandCycle>(result.Error);
        Assert.Equal(SpanU, cycle.Span);
        Assert.Equal(2, budget.ResolutionRetries);    // L's projection, then U's (re-entering) VALUE
        Assert.Equal(2, attempts);                    // L's resolver: pending U, then the replay
        Assert.Equal(1, evaluations);
        Assert.True(u.HasCompletedValue);
        Assert.Equal(1, l.ProjectionComputations);
        Assert.True(l.HasCallableMemo);
        Assert.Equal(cycle, l.ProjectCallable().Error);
        Assert.True(l.ProjectCallable().Error.IsProjectionFailure);
        Assert.Equal(0, u.ActiveDependencyCount);
        Assert.Equal(0, l.ProjectionActiveDependencyCount);
        Assert.False(NeedNode.HasCurrentNode);
        Assert.Equal(0, budget.ConsumedSteps);

        // The synchronous oracle of the same shape.
        var syncBudget = NewBudget();
        NeedCell? su = null, sl = null;
        sl = Runtime(syncBudget, () => ThenIdentity(su!.Demand(), Identity()), span: SpanA);
        su = ValueCell(syncBudget, () => { var c = sl.ProjectCallable(); return c.IsError ? c.Error : One; }, span: SpanU);
        Assert.Equal(result, su.Demand());
    }

    [Fact]
    public async Task CallableSelfReentry_ThroughTheResolver_IsDemandCycle()
    {
        var budget = NewBudget(asynchronous: true);
        NeedCell? a = null;
        a = Runtime(budget, () => a!.ProjectCallable(),
            async () => { await Task.Yield(); return await ResolveAsync(budget, () => a!.ProjectCallable()); }, SpanA);
        var result = await ResolveAsync(budget, () => a.ProjectCallable()).AsTask().WaitAsync(WaitLimit);
        Assert.Equal(SpanA, Assert.IsType<EvalError.DemandCycle>(result.Error).Span);
        Assert.Equal(1, a.ProjectionComputations);
        Assert.True(a.HasCallableMemo);
        Assert.Equal(2, budget.ResolutionRetries);
        Assert.Equal(0, a.ProjectionActiveDependencyCount);
    }

    [Fact]
    public async Task CallableValueCallable_ThroughTheResolver_IsDemandCycle()
    {
        var budget = NewBudget(asynchronous: true);
        NeedCell? a = null, r = null;
        var evaluations = 0;
        r = ValueCell(budget, () => One, async () =>
        {
            evaluations++;
            await Task.Yield();
            var p = await ResolveAsync(budget, () => a!.ProjectCallable());
            return p.IsError ? p.Error : One;
        }, SpanU);
        a = Runtime(budget, Identity, () => ResolveAsync(budget, () => ThenIdentity(r.Demand(), Identity())), SpanA);
        var result = await a.ProjectCallableAsync().AsTask().WaitAsync(WaitLimit);
        Assert.Equal(SpanA, Assert.IsType<EvalError.DemandCycle>(result.Error).Span);
        Assert.Equal(1, evaluations);
        Assert.True(r.HasCompletedValue);
        Assert.Equal(0, r.ActiveDependencyCount);
        Assert.Equal(0, a.ProjectionActiveDependencyCount);
    }

    [Fact]
    public async Task TwoCellCallableCycle_ThroughTheResolver_IsDemandCycleAtTheReenteredCell()
    {
        var budget = NewBudget(asynchronous: true);
        NeedCell? a = null, b = null;
        a = Runtime(budget, () => b!.ProjectCallable(), () => ResolveAsync(budget, () => b!.ProjectCallable()), SpanA);
        b = Runtime(budget, () => a.ProjectCallable(), () => ResolveAsync(budget, () => a.ProjectCallable()), SpanB);
        var result = await ResolveAsync(budget, () => a.ProjectCallable()).AsTask().WaitAsync(WaitLimit);
        Assert.Equal(SpanA, Assert.IsType<EvalError.DemandCycle>(result.Error).Span);
        Assert.Equal(1, a.ProjectionComputations);
        Assert.Equal(1, b.ProjectionComputations);
    }

    [Fact]
    public async Task StickyOrdinaryFailure_IsReobservedWithoutAnyFurtherStep()
    {
        var budget = NewBudget(asynchronous: true);
        var evaluations = 0;
        var receiver = ValueCell(budget, () => { evaluations++; return new EvalError.DivByZero { Span = SpanU }; });
        var a = Runtime(budget, () => ThenIdentity(receiver.Demand(), Identity()),
            () => ResolveAsync(budget, () => ThenIdentity(receiver.Demand(), Identity())));
        var first = await ResolveAsync(budget, () => a.ProjectCallable());
        var retries = budget.ResolutionRetries;
        var second = await ResolveAsync(budget, () => a.ProjectCallable());
        Assert.IsType<EvalError.DivByZero>(first.Error);
        Assert.Equal(first, second);
        Assert.Equal(retries, budget.ResolutionRetries);
        Assert.Equal(1, evaluations);
        Assert.Equal(1, a.ProjectionComputations);
    }

    [Fact]
    public async Task NoncyclicValueAndCallableSteps_AdvanceOnceEach()
    {
        var budget = NewBudget(asynchronous: true);
        var r = ValueCell(budget, () => One, async () => { await Task.Yield(); return One; });
        var a = Runtime(budget, Identity, async () => { await Task.Yield(); return Identity(); });
        var valueResult = await ResolveAsync(budget, () => ThenIdentity(r.Demand(), Identity()));
        Assert.Same(IdentityAlgorithm, valueResult.Value);
        Assert.Equal(1, budget.ResolutionRetries);
        var callableResult = await ResolveAsync(budget, () => a.ProjectCallable());
        Assert.Same(IdentityAlgorithm, callableResult.Value);
        Assert.Equal(2, budget.ResolutionRetries);
        Assert.True(a.HasCallableMemo);
    }

    [Fact]
    public async Task SuccessfulAbsence_IsOkNull_StaticAndRuntime()
    {
        var budget = NewBudget(asynchronous: true);
        var leaf = new NeedCell(() => One, () => new(One), () => EvalResult<Algorithm?>.Ok(null), budget: budget);
        var runtime = Runtime(budget, () => EvalResult<Algorithm?>.Ok(null), async () => { await Task.Yield(); return EvalResult<Algorithm?>.Ok(null); });
        var staticAbsence = await ResolveAsync(budget, () => leaf.ProjectCallable());
        var runtimeAbsence = await ResolveAsync(budget, () => runtime.ProjectCallable());
        Assert.True(staticAbsence.IsOk);
        Assert.Null(staticAbsence.Value);
        Assert.True(runtimeAbsence.IsOk);
        Assert.Null(runtimeAbsence.Value);
    }

    [Fact]
    public async Task Cancellation_EndsTheResolutionWithTheOriginalToken_PublishingNothing()
    {
        using var stop = new CancellationTokenSource();
        var budget = NewBudget(asynchronous: true, token: stop.Token);
        var r = ValueCell(budget, () => One, async () =>
        {
            await Task.Yield();
            stop.Cancel();
            stop.Token.ThrowIfCancellationRequested();
            return One;
        }, token: stop.Token);
        var a = Runtime(budget, Identity, () => ResolveAsync(budget, () => ThenIdentity(r.Demand(), Identity())), token: stop.Token);
        var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(async () => await ResolveAsync(budget, () => a.ProjectCallable()));
        Assert.Equal(stop.Token, error.CancellationToken);
        Assert.False(a.HasCallableMemo);
        Assert.Equal(0, a.ProjectionActiveDependencyCount);
        Assert.Equal(0, r.ActiveDependencyCount);
        Assert.False(NeedCell.IsObserving);
        Assert.False(NeedNode.HasCurrentNode);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task HostException_EndsResolutionAndRemainsStickyOnBothChannels(bool callable)
    {
        var budget = NewBudget(asynchronous: true);
        var failure = new InvalidOperationException("projection dependency failed");
        var computations = 0;
        var value = ValueCell(budget, () => throw failure, async () =>
        {
            computations++;
            await Task.Yield();
            throw failure;
        });
        var projection = Runtime(budget, () => throw failure, async () =>
        {
            computations++;
            await Task.Yield();
            throw failure;
        });
        EvalResult<Algorithm?> Resolve()
            => callable ? projection.ProjectCallable() : ThenIdentity(value.Demand(), Identity());

        var first = await Assert.ThrowsAsync<InvalidOperationException>(async () => await ResolveAsync(budget, Resolve));
        var retries = budget.ResolutionRetries;
        var second = await Assert.ThrowsAsync<InvalidOperationException>(async () => await ResolveAsync(budget, Resolve));
        Assert.Same(failure, first);
        Assert.Same(failure, second);
        Assert.Equal(1, computations);
        Assert.Equal(1, retries);
        Assert.Equal(retries, budget.ResolutionRetries);
        Assert.False(projection.HasCallableMemo);
        Assert.False(projection.HasProjectionInFlight);
        Assert.Equal(0, projection.ProjectionActiveDependencyCount);
        Assert.Equal(0, value.ActiveDependencyCount);
        Assert.False(NeedCell.IsObserving);
        Assert.False(NeedNode.HasCurrentNode);
        Assert.Equal(0, budget.ConsumedSteps);
    }

    [Fact]
    public async Task TerminalResourceOutcome_IsReplayed_AndNothingStartsAfterwards()
    {
        var budget = NewBudget(asynchronous: true);
        var r = ValueCell(budget, () => One, async () =>
        {
            await Task.Yield();
            return new EvalError.EvaluationStepLimitExceeded(7);
        });
        var a = Runtime(budget, Identity, () => ResolveAsync(budget, () => ThenIdentity(r.Demand(), Identity())));
        var other = Runtime(budget, Identity);
        var result = await ResolveAsync(budget, () => a.ProjectCallable());
        var limit = Assert.IsType<EvalError.EvaluationStepLimitExceeded>(result.Error);
        Assert.False(limit.IsProjectionFailure);   // the run's retained object, never re-marked
        Assert.Same(limit, budget.CheckContinuation());
        var after = await ResolveAsync(budget, () => other.ProjectCallable());
        Assert.Same(limit, after.Error);
        Assert.Equal(0, other.ProjectionComputations);
    }

    [Fact]
    public async Task SharedNoncyclicDependency_HasNoFalseCycle_AndComputesTheSharedCellsOnce()
    {
        var budget = NewBudget(asynchronous: true);
        var evaluations = 0;
        var receiver = ValueCell(budget, () => One, async () => { Interlocked.Increment(ref evaluations); await Task.Yield(); return One; });
        var d = Runtime(budget, Identity, () => ResolveAsync(budget, () => ThenIdentity(receiver.Demand(), Identity())));
        var b = Runtime(budget, () => d.ProjectCallable(), () => ResolveAsync(budget, () => d.ProjectCallable()));
        var c = Runtime(budget, () => d.ProjectCallable(), () => ResolveAsync(budget, () => d.ProjectCallable()));
        var a = Runtime(budget, Identity, () => ResolveAsync(budget, () =>
        {
            var left = b.ProjectCallable();
            if (left.IsError) return left;
            return c.ProjectCallable();
        }));
        var result = await ResolveAsync(budget, () => a.ProjectCallable()).AsTask().WaitAsync(WaitLimit);
        Assert.Same(IdentityAlgorithm, result.Value);
        Assert.Equal(1, evaluations);
        Assert.Equal(1, d.ProjectionComputations);
        Assert.Equal(1, b.ProjectionComputations);
        Assert.Equal(1, c.ProjectionComputations);
    }

    [Fact]
    public async Task LongValidProjectionChain_CompletesWithOneStepPerLink()
    {
        const int length = 200;
        var budget = NewBudget(asynchronous: true);
        var cells = new NeedCell[length];
        cells[length - 1] = Runtime(budget, Identity, async () => { await Task.Yield(); return Identity(); });
        for (var i = length - 2; i >= 0; i--)
        {
            var next = cells[i + 1];
            cells[i] = Runtime(budget, () => next.ProjectCallable(), () => ResolveAsync(budget, () => next.ProjectCallable()));
        }
        var result = await ResolveAsync(budget, () => cells[0].ProjectCallable()).AsTask().WaitAsync(WaitLimit);
        Assert.Same(IdentityAlgorithm, result.Value);
        Assert.Equal(length, budget.ResolutionRetries);
        Assert.All(cells, cell => Assert.Equal(1, cell.ProjectionComputations));
    }

    // ── Async consumers in the production evaluator ─────────────────────────────────────────

    private sealed record Run(EvalResult<Evaluator.CountedResult> Result, long Steps, int Computations, long Retries);

    // One program over a parameter `f` (and `p`) bound to a runtime projection, on the sync
    // engine (generic) and on the async twin.
    private static async Task<(Run Sync, Run Async)> SyncAndAsync(Expr program,
        Func<EvaluationBudget, NeedCell> projection, string name = "f")
    {
        var syncBudget = NewBudget();
        var syncCell = projection(syncBudget);
        var sync = Evaluator.EvalCounted(program, Ctx(syncBudget, (name, syncCell)), []);
        var asyncBudget = NewBudget(asynchronous: true);
        var asyncCell = projection(asyncBudget);
        var asynchronous = await EvalAsync(program, Ctx(asyncBudget, (name, asyncCell)));
        Assert.False(NeedCell.IsObserving);
        Assert.False(NeedNode.HasCurrentNode);
        return (new(sync, syncBudget.ConsumedSteps, syncCell.ProjectionComputations, syncBudget.ResolutionRetries),
            new(asynchronous, asyncBudget.ConsumedSteps, asyncCell.ProjectionComputations, asyncBudget.ResolutionRetries));
    }

    private static void AssertAgree((Run Sync, Run Async) runs)
    {
        Assert.Equal(Show(runs.Sync.Result), Show(runs.Async.Result));
        if (runs.Sync.Result.IsError)
        {
            Assert.Equal(runs.Sync.Result.Error, runs.Async.Result.Error);
            Assert.Equal(runs.Sync.Result.Error.Span, runs.Async.Result.Error.Span);
            Assert.Equal(KatLangError.FromEvalError(runs.Sync.Result.Error).Message, KatLangError.FromEvalError(runs.Async.Result.Error).Message);
        }
        Assert.Equal(runs.Sync.Steps, runs.Async.Steps);
        Assert.Equal(runs.Sync.Computations, runs.Async.Computations);
        Assert.Equal(0, runs.Sync.Retries);
    }

    private static Func<EvaluationBudget, NeedCell> Projecting(Func<EvalResult<Algorithm?>> outcome)
        => budget => Runtime(budget, outcome, async () => { await Task.Yield(); return outcome(); }, SpanA);

    private static Expr Builtin(BuiltinId id) => new Expr.AlgorithmExpr(new Algorithm.Builtin(id));

    private static Expr List(params int[] items) => new Expr.ListLiteral(items.Select(i => (Expr)new Expr.Num(i)).ToArray());

    // B = { G(x) = x; V = 7; 0 }
    private static readonly Algorithm.User Box = new(null, [], [],
        [new Property("G", IdentityAlgorithm), new Property("V", new Algorithm.User(null, [], [], [], [new Expr.Num(7)]))],
        [new Expr.Num(0)]);

    // R(acc, x) = x;  P(x) = true
    private static readonly Algorithm.User Reducer = new(null, [new CaptureParameterPattern("acc"), new CaptureParameterPattern("x")], [], [], [new Expr.Param("x")]);
    private static readonly Algorithm.User Predicate = new(null, [new CaptureParameterPattern("x")], [], [], [new Expr.BoolLiteral(true)]);

    // F(g) = map([1, 2], g); the forwarding hop transports the projected cell.
    private static readonly Algorithm.User ForwardingMapper = new(null, [new CaptureParameterPattern("g")], [], [],
        [new Expr.Call(Builtin(BuiltinId.@map), [List(1, 2), new Expr.Param("g")])]);

    // The outer map invokes a callback whose body invokes another map with captured f.
    private static readonly Algorithm.User NestedMapper = new(null, [new CaptureParameterPattern("x")], [], [],
        [new Expr.Call(Builtin(BuiltinId.@map), [List(1, 2), new Expr.Param("f")])]);

    private static readonly Algorithm.Conditional IdentityFamily = new(null, [],
        [new CondBranch(new Pattern.SequenceValue([new Pattern.Bind("x")]),
            new Algorithm.User(null, [], [], [], [new Expr.Param("x")]))]);

    private static readonly Algorithm.User IncrementingWhileStep = new(null, [new CaptureParameterPattern("x")], [], [],
        [new Expr.Binary(BinaryOp.Add, new Expr.Param("x"), new Expr.Num(1)),
            new Expr.Comparison(new Expr.Param("x"), [new ComparisonLink(ComparisonOp.Lt, new Expr.Num(2))])]);

    public static TheoryData<string> Routes =>
    [
        "callee", "map", "filter", "reduce", "repeat", "while-failure", "dot-receiver-call", "dot-callee",
        "dot-string-member", "lexical-fallback", "supplied-dot-path-callback",
        "forwarded-map", "nested-map", "family-map", "while-success",
    ];

    private static (Expr Program, Func<EvaluationBudget, NeedCell> Projection, string Name, string Expected) Route(string route) => route switch
    {
        "callee" => (new Expr.Call(new Expr.Param("f"), [new Expr.Num(3)]), Projecting(Identity), "f", "ok 3"),
        "map" => (new Expr.Call(Builtin(BuiltinId.@map), [List(1, 2), new Expr.Param("f")]), Projecting(Identity), "f", "ok L[1, 2]"),
        "filter" => (new Expr.Call(Builtin(BuiltinId.@filter), [List(1, 2), new Expr.Param("f")]),
            Projecting(() => EvalResult<Algorithm?>.Ok(Predicate)), "f", "ok L[1, 2]"),
        "reduce" => (new Expr.Call(Builtin(BuiltinId.@reduce), [List(1, 2), new Expr.Param("f"), new Expr.Num(0)]),
            Projecting(() => EvalResult<Algorithm?>.Ok(Reducer)), "f", "ok"),
        "repeat" => (new Expr.Call(Builtin(BuiltinId.@repeat), [new Expr.Call(new Expr.Param("f"), [new Expr.Num(5)]), new Expr.Num(2)]), Projecting(Identity), "f", "ok 5"),
        "while-failure" => (new Expr.Call(Builtin(BuiltinId.@while), [new Expr.Call(new Expr.Param("f"), [new Expr.Num(0)])]),
            Projecting(() => new EvalError.IllegalInEval("step projection failed") { Span = SpanB }), "f", "err"),
        "dot-receiver-call" => (new Expr.DotCall(new Expr.Param("p"), "G", [new Expr.Num(3)]), Projecting(() => EvalResult<Algorithm?>.Ok(Box)), "p", "ok 3"),
        "dot-callee" => (new Expr.Call(new Expr.DotCall(new Expr.Param("p"), "G"), [new Expr.Num(3)]), Projecting(() => EvalResult<Algorithm?>.Ok(Box)), "p", "ok 3"),
        "dot-string-member" => (new Expr.DotCall(new Expr.DotCall(new Expr.Param("p"), "V"), "string"), Projecting(() => EvalResult<Algorithm?>.Ok(Box)), "p", "ok '7'"),
        "lexical-fallback" => (new Expr.DotCall(new Expr.Num(3), "f") { LexicalFallback = new Expr.Param("f") }, Projecting(Identity), "f", "ok 3"),
        "supplied-dot-path-callback" => (new Expr.Call(Builtin(BuiltinId.@map), [List(1, 2), new Expr.DotCall(new Expr.Param("p"), "G")]),
            Projecting(() => EvalResult<Algorithm?>.Ok(Box)), "p", "ok L[1, 2]"),
        "forwarded-map" => (new Expr.Call(new Expr.AlgorithmExpr(ForwardingMapper), [new Expr.Param("f")]),
            Projecting(Identity), "f", "ok L[1, 2]"),
        "nested-map" => (new Expr.Call(Builtin(BuiltinId.@map), [List(0), new Expr.AlgorithmExpr(NestedMapper)]),
            Projecting(Identity), "f", "ok L[L[1, 2]]"),
        "family-map" => (new Expr.Call(Builtin(BuiltinId.@map), [List(1, 2), new Expr.Param("f")]),
            Projecting(() => EvalResult<Algorithm?>.Ok(IdentityFamily)), "f", "ok L[1, 2]"),
        "while-success" => (new Expr.Call(Builtin(BuiltinId.@while), [new Expr.Call(new Expr.Param("f"), [new Expr.Num(0)])]),
            Projecting(() => EvalResult<Algorithm?>.Ok(IncrementingWhileStep)), "f", "ok 2"),
        _ => throw new ArgumentOutOfRangeException(nameof(route)),
    };

    // §13 route coverage: every representative async CALLABLE route reaches the runtime
    // projection through the async resolution adapter or an awaiting consumer — an unrouted
    // synchronous projection in the async run would throw the fail-loud guard — and agrees with
    // the synchronous engine on value, structured error, steps and computations.
    [Theory]
    [MemberData(nameof(Routes))]
    public async Task EveryAsyncCallableRoute_ResolvesTheRuntimeProjectionThroughTheAdapter_AndAgreesWithSync(string route)
    {
        var (program, projection, name, expected) = Route(route);
        var runs = await SyncAndAsync(program, projection, name);
        AssertAgree(runs);
        Assert.StartsWith(expected, Show(runs.Async.Result));
        Assert.Equal(1, runs.Async.Computations);
        Assert.True(runs.Async.Retries >= 1, $"the async run awaited the runtime projection ({runs.Async.Retries})");
    }

    [Fact]
    public async Task ZeroIterationRepeat_NeverProjectsItsRuntimeStep()
    {
        var program = new Expr.Call(Builtin(BuiltinId.@repeat), [new Expr.Call(new Expr.Param("f"), [new Expr.Num(5)]), new Expr.Num(0)]);
        var runs = await SyncAndAsync(program, Projecting(Identity));
        AssertAgree(runs);
        Assert.Equal("ok 5", Show(runs.Async.Result));
        Assert.Equal(0, runs.Async.Computations);
        Assert.Equal(0, runs.Async.Retries);
    }

    [Fact]
    public async Task OptimizedSyncLoop_AgreesWithTheGenericAndAsyncLoopsOverARuntimeStep()
    {
        var program = new Expr.Call(Builtin(BuiltinId.@repeat), [new Expr.Call(new Expr.Param("f"), [new Expr.Num(5)]), new Expr.Num(3)]);
        var budget = NewBudget();
        var cell = Projecting(Identity)(budget);
        var loops = new LoopOptimizationDiagnostics();
        var optimized = Evaluator.EvalCounted(program, Ctx(budget, ("f", cell)) with { EnableLoopOptimization = true, LoopDiagnostics = loops }, []);
        var runs = await SyncAndAsync(program, Projecting(Identity));
        AssertAgree(runs);
        Assert.Equal(Show(runs.Sync.Result), Show(optimized));
        Assert.Equal(runs.Sync.Steps, budget.ConsumedSteps);
        Assert.Equal(1, cell.ProjectionComputations);
        Assert.Equal(1, loops.GetSnapshot().OptimizedLoopHits);
    }

    [Fact]
    public async Task StepBudget_IsChargedIdenticallyOnBothEngines_AtEveryLimit()
    {
        var program = new Expr.Call(Builtin(BuiltinId.@repeat), [new Expr.Call(new Expr.Param("f"), [new Expr.Num(5)]), new Expr.Num(3)]);
        for (var limit = 1; limit <= 12; limit++)
        {
            var limits = new EvaluationLimits { MaxSteps = limit };
            var syncBudget = NewBudget(limits: limits);
            var sync = Evaluator.EvalCounted(program, Ctx(syncBudget, ("f", Projecting(Identity)(syncBudget))), []);
            var asyncBudget = NewBudget(asynchronous: true, limits: limits);
            var asynchronous = await EvalAsync(program, Ctx(asyncBudget, ("f", Projecting(Identity)(asyncBudget))));
            Assert.Equal(Show(sync), Show(asynchronous));
            Assert.Equal(syncBudget.ConsumedSteps, asyncBudget.ConsumedSteps);
        }
    }

    // A callback / loop step re-entered inside its own projection: the projection demands the
    // VALUE whose evaluation is consuming it (R2 Q5). Sync and async both report DemandCycle.
    [Theory]
    [InlineData("map")]
    [InlineData("reduce")]
    [InlineData("repeat")]
    [InlineData("callee")]
    public async Task ProjectionReenteringItsConsumersValue_IsDemandCycle_OnBothEngines(string consumer)
    {
        Expr program = consumer switch
        {
            "map" => new Expr.Call(Builtin(BuiltinId.@map), [List(1), new Expr.Param("f")]),
            "reduce" => new Expr.Call(Builtin(BuiltinId.@reduce), [List(1), new Expr.Param("f"), new Expr.Num(0)]),
            "repeat" => new Expr.Call(Builtin(BuiltinId.@repeat), [new Expr.Call(new Expr.Param("f"), [new Expr.Num(0)]), new Expr.Num(1)]),
            _ => new Expr.Call(new Expr.Param("f"), [new Expr.Num(3)]),
        };
        async Task<(EvalResult<Evaluator.CountedResult> Result, NeedCell Owner, NeedCell Projection, long Steps)> Observe(bool asynchronous)
        {
            var budget = NewBudget(asynchronous);
            NeedCell? owner = null;
            var projection = Runtime(budget, () => ThenIdentity(owner!.Demand(), Identity()),
                async () => { await Task.Yield(); return ThenIdentity(await owner!.DemandAsync(), Identity()); }, SpanA);
            var ctx = Ctx(budget, ("f", projection));
            owner = ValueCell(budget, () => Evaluator.EvalCounted(program, ctx, []),
                async () => await EvalAsync(program, ctx), SpanU);
            var result = asynchronous ? await owner.DemandAsync().AsTask().WaitAsync(WaitLimit) : owner.Demand();
            return (result, owner, projection, budget.ConsumedSteps);
        }
        var sync = await Observe(false);
        var asynchronous = await Observe(true);
        Assert.Equal(SpanU, Assert.IsType<EvalError.DemandCycle>(Innermost(sync.Result.Error)).Span);
        Assert.Equal(sync.Result.Error, asynchronous.Result.Error);
        Assert.Equal(KatLangError.FromEvalError(sync.Result.Error).Message, KatLangError.FromEvalError(asynchronous.Result.Error).Message);
        Assert.Equal(sync.Steps, asynchronous.Steps);
        Assert.Equal(1, asynchronous.Projection.ProjectionComputations);
        Assert.True(asynchronous.Owner.HasCompletedValue);
        Assert.Equal(0, asynchronous.Owner.ActiveDependencyCount);
        Assert.Equal(0, asynchronous.Projection.ProjectionActiveDependencyCount);
    }

    [Fact]
    public async Task RepeatedNameBinder_ConsumesBothAwaitedProjections()
    {
        // F(f, f) = f(3), supplied (g, g) with g a runtime projection: equal VALUEs, the same
        // callable identity on both contributions.
        var body = new Algorithm.User(null, [new CaptureParameterPattern("f"), new CaptureParameterPattern("f")], [], [],
            [new Expr.Call(new Expr.Param("f"), [new Expr.Num(3)])]);
        var program = new Expr.Call(new Expr.AlgorithmExpr(body), [new Expr.Param("g"), new Expr.Param("g")]);
        var runs = await SyncAndAsync(program, Projecting(Identity), "g");
        AssertAgree(runs);
        Assert.Equal("ok 3", Show(runs.Async.Result));
        Assert.Equal(1, runs.Async.Computations);
    }

    [Fact]
    public async Task AsyncCancellationInsideARuntimeProjection_PropagatesTheOriginalToken()
    {
        using var stop = new CancellationTokenSource();
        var budget = NewBudget(asynchronous: true, token: stop.Token);
        var cell = Runtime(budget, Identity, async () =>
        {
            await Task.Yield();
            stop.Cancel();
            stop.Token.ThrowIfCancellationRequested();
            return Identity();
        }, SpanA, stop.Token);
        var program = new Expr.Call(Builtin(BuiltinId.@map), [List(1), new Expr.Param("f")]);
        var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(() => EvalAsync(program, Ctx(budget, ("f", cell))));
        Assert.Equal(stop.Token, error.CancellationToken);
        Assert.False(cell.HasCallableMemo);
        Assert.Equal(0, cell.ProjectionActiveDependencyCount);
        Assert.False(NeedCell.IsObserving);
    }

    // ── Failure provenance ──────────────────────────────────────────────────────────────────

    [Fact]
    public void RuntimeProjectionFailure_IsMarked_EqualityTransparently_AndAbsenceIsNot()
    {
        var budget = NewBudget();
        var failure = new EvalError.NotAnAlgorithm("inner") { Span = SpanB };
        var failed = Runtime(budget, () => failure).ProjectCallable().Error;
        Assert.True(failed.IsProjectionFailure);
        Assert.Equal(failure, failed);
        Assert.Equal(failure.GetHashCode(), failed.GetHashCode());
        Assert.Equal(failure.Code, failed.Code);
        Assert.Equal(KatLangError.FromEvalError(failure).Message, KatLangError.FromEvalError(failed).Message);
        Assert.Equal(SpanB, failed.Span);
        Assert.True((failed with { Span = SpanA }).IsProjectionFailure);
        Assert.True(Evaluator.IsProjectionFailure(new EvalError.WithContext("outer", failed)));
        Assert.False(Evaluator.IsAbsentIdentity(failed));
        Assert.True(Evaluator.IsAbsentIdentity(failure));
        // Identity-only projections are never marked; neither is a re-entry observation.
        var identityOnly = new NeedCell(() => One, () => new(One), () => failure, budget: budget);
        Assert.False(identityOnly.ProjectCallable().Error.IsProjectionFailure);
        Assert.True(Runtime(budget, () => EvalResult<Algorithm?>.Ok(null)).ProjectCallable() is { IsOk: true, Value: null });
    }

    public static TheoryData<string, string> ProvenanceCases => new()
    {
        { "callee", "IllegalInEval" },
        { "callee", "TypeMismatch" },
        { "callee", "NotAnAlgorithm" },
        { "callee", "Wrapped" },
        { "dot-callee", "IllegalInEval" },
        { "dot-callee", "NotAnAlgorithm" },
        { "dot-receiver-call", "NotAnAlgorithm" },
        { "dot-receiver-call", "IllegalInEval" },
        { "map", "NotAnAlgorithm" },
        { "supplied-dot-path-callback", "IllegalInEval" },
        { "supplied-dot-path-callback", "NotAnAlgorithm" },
        { "repeat", "IllegalInEval" },
        { "while-failure", "NotAnAlgorithm" },
        { "forwarded-map", "IllegalInEval" },
        { "nested-map", "NotAnAlgorithm" },
        { "family-map", "TypeMismatch" },
    };

    private static EvalError ProvenanceFailure(string kind) => kind switch
    {
        "IllegalInEval" => new EvalError.IllegalInEval("min requires a non-empty collection") { Span = SpanB },
        "TypeMismatch" => new EvalError.TypeMismatch("not a reference") { Span = SpanB },
        "NotAnAlgorithm" => new EvalError.NotAnAlgorithm("inner") { Span = SpanB },
        _ => new EvalError.WithContext("Bad", new EvalError.IllegalInEval("inner failure") { Span = SpanB }) { Span = SpanB },
    };

    // A runtime projection's failure keeps its kind, payload, span and context through every
    // route — never replaced by "no identity" (`param(f)`, `dot result`, a slot role, a value
    // receiver route) — identically on both engines.
    [Theory]
    [MemberData(nameof(ProvenanceCases))]
    public async Task RuntimeProjectionFailure_KeepsItsOriginOnEveryRoute(string route, string kind)
    {
        var (program, _, name, _) = Route(route);
        var failure = ProvenanceFailure(kind);
        var runs = await SyncAndAsync(program, Projecting(() => failure), name);
        AssertAgree(runs);
        var observed = runs.Async.Result.Error;
        Assert.True(Evaluator.IsProjectionFailure(observed), observed.ToString());
        var innermost = Innermost(observed);
        Assert.Equal(Innermost(failure), innermost);
        Assert.Equal(SpanB, innermost.Span);
        Assert.Equal(1, runs.Async.Computations);
    }

    [Fact]
    public async Task StaticAbsence_IsUnchanged_AndRuntimeAbsenceReportsTheSameAbsence()
    {
        var program = new Expr.Call(new Expr.Param("f"), [new Expr.Num(3)]);
        var staticBudget = NewBudget();
        var staticCell = new NeedCell(() => One, () => new(One), () => EvalResult<Algorithm?>.Ok(null), span: SpanA, budget: staticBudget);
        var staticResult = Evaluator.EvalCounted(program, Ctx(staticBudget, ("f", staticCell)), []);
        var staticAbsence = Assert.IsType<EvalError.NotAnAlgorithm>(Innermost(staticResult.Error));
        Assert.Equal("param(f)", staticAbsence.Description);
        Assert.False(Evaluator.IsProjectionFailure(staticResult.Error));
        var runs = await SyncAndAsync(program, Projecting(() => EvalResult<Algorithm?>.Ok(null)));
        AssertAgree(runs);
        Assert.Equal(staticResult.Error, runs.Async.Result.Error);
        Assert.False(Evaluator.IsProjectionFailure(runs.Async.Result.Error));

        // A static (unmarked) value receiver keeps the value-receiver route.
        var dotProgram = new Expr.Call(new Expr.DotCall(new Expr.Param("p"), "G"), [new Expr.Num(3)]);
        var dotBudget = NewBudget();
        var valueReceiver = NeedCell.Ready(new(new Result.Atom(5), 1));
        var dotResult = Evaluator.EvalCounted(dotProgram, Ctx(dotBudget, ("p", valueReceiver)), []);
        Assert.Equal("dot result", Assert.IsType<EvalError.NotAnAlgorithm>(Innermost(dotResult.Error)).Description);
    }
}
