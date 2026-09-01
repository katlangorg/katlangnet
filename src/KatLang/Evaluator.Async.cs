using System.Numerics;
using System.Runtime.CompilerServices;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using KatLang.Optimizations.Loops;
using KatLang.Optimizations.Sequences;

namespace KatLang;

/// <summary>
/// Asynchronous evaluation surface and the async TWIN FAMILY of the counted evaluator.
///
/// <para><b>Architecture ("sync-delegating async twin spine").</b> The synchronous
/// evaluator in <c>Evaluator.cs</c> remains the semantic oracle. The async entry points
/// below decide ONCE per run which execution family drives evaluation:</para>
/// <list type="number">
///   <item><b>Fast path</b> — when no run component can complete asynchronously (the
///   zero-argument property cache does not implement
///   <see cref="IAsyncZeroArgPropertyResultCache"/> and no ASYNCHRONOUS
///   <see cref="HostOperation"/> is configured — every configuration without async
///   host operations), the async entry point executes the ORDINARY synchronous pipeline
///   inline on the calling thread and returns an already-completed task. Behavior,
///   budget accounting, optimizer strategy selection, stack shape, and cancellation are
///   those of the synchronous entry point, by identity — the same code runs. There is no
///   thread offloading and no artificial yielding.</item>
///   <item><b>Async twin path</b> — when a run component IS async-capable, evaluation
///   runs through the <c>*Async</c> twin methods in this file. Each twin MIRRORS its
///   synchronous counterpart's sequencing exactly (marked <c>// MIRROR OF ...</c>) and
///   must be kept in lock-step with it; the twins share every non-evaluating helper
///   (lookup, binding matchers, budget chokepoints, value construction, diagnostics)
///   with the synchronous family and re-implement only the child-evaluation sequencing
///   that must be awaitable. A genuinely asynchronous host operation — the internal
///   cache seam, or a public asynchronous <see cref="HostOperation"/> awaited at its
///   wrapper-body site — suspends the whole spine and resumes it on completion.</item>
/// </list>
///
/// <para><b>Twin discipline.</b> A twin may call: other <c>*Async</c> twins; shared
/// helpers verified not to evaluate expressions; and the plain synchronous
/// <see cref="Eval"/> only where the dispatched kind is a proven leaf (see
/// <see cref="EvalCountedAsync"/>'s explicitly enumerated sync-delegable leaf
/// group; the dispatch default is a fail-loud exhaustiveness guard, so a new
/// recursive <see cref="Expr"/> variant can never silently fall through to
/// synchronous child evaluation). Twins are COUNTED-family mirrors;
/// where the synchronous code used a plain-evaluation wrapper, the twin awaits the
/// counted core and projects its value — every such wrapper in the synchronous family is
/// itself exactly that projection (for example <c>EvalAlgOutput</c> →
/// <c>EvalAlgOutputCountedCore</c> → <c>ProjectCountedValue</c>), and the plain/counted value
/// equivalence is a Lean-modelled language invariant pinned by the explorer corpus.
/// The async differential suites re-pin the equivalence empirically across the language
/// corpora.</para>
///
/// <para><b>Strategy pinning.</b> The twin path always creates its root context with
/// loop optimization and sequence-pipeline fusion DISABLED, so the twins only ever
/// mirror the generic strategies. This is the same generic-strategies mode that
/// configured step/string/materialization budgets already force on the synchronous path,
/// and the budget architecture guarantees strategy independence of every limit verdict
/// (see <c>CreateRootCtx</c>), so results and verdicts are unchanged; only internal
/// diagnostics observations (which honestly record the generic strategy) differ. The
/// optimized executors can be taught to cooperate with the twin family later without any
/// architectural change.</para>
///
/// <para><b>Cancellation.</b> Identical to the synchronous contract: the run token lives
/// on the shared <see cref="EvaluationBudget"/> and is observed at the same chokepoints
/// (which are shared code), plus once at entry and once before completion. Requested
/// cancellation escapes as <see cref="OperationCanceledException"/> carrying the supplied
/// token — surfaced through the returned task, as an async API surfaces exceptions — and
/// is never converted into an <see cref="EvalError"/> or retained binding value.</para>
///
/// <para><b>Stack.</b> The synchronous family's calibrated stack behavior is untouched.
/// The twin family runs the same dynamic-depth budget with the same
/// <c>TryEnsureSufficientExecutionStack</c> backstop, so a synchronously-completing twin
/// chain that outgrows the host stack fails with the same structured
/// <see cref="EvalError.EvaluationStackExhausted"/>. A genuine suspension unwinds the
/// evaluator frames that led to the await; the awaitable and runtime decide which thread
/// and stack later run the continuation, so the twin-only stack probes remain necessary
/// after resumption too. The async structural-depth probes in the test suite characterize
/// the twin path's headroom separately.</para>
/// </summary>
public static partial class Evaluator
{
    // ── Async entry points (public) ─────────────────────────────────────────

    /// <summary>
    /// Asynchronous counterpart of <see cref="Run(Expr)"/>. See
    /// <see cref="RunAsync(Expr, EvaluationLimits?, CancellationToken)"/> for the
    /// contract.
    /// </summary>
    public static Task<EvalResult<Result>> RunAsync(Expr expr)
        => RunAsync(expr, limits: null);

    /// <summary>
    /// Asynchronous counterpart of <see cref="Run(Expr, EvaluationLimits?)"/>. See
    /// <see cref="RunAsync(Expr, EvaluationLimits?, CancellationToken)"/> for the
    /// contract.
    /// </summary>
    public static Task<EvalResult<Result>> RunAsync(Expr expr, EvaluationLimits? limits)
        => RunAsync(expr, limits, cancellationToken: default);

    /// <summary>
    /// Asynchronous counterpart of <see cref="Run(Expr, EvaluationLimits?, CancellationToken)"/>.
    ///
    /// <para>An uncancelled run produces exactly the result, diagnostics, and limit
    /// verdict of the synchronous overload. This overload carries no asynchronous host
    /// component, so the returned task completes synchronously on the calling thread:
    /// this method never schedules evaluation onto another thread and never yields
    /// artificially — host scheduling (thread placement, offloading) remains the host's
    /// responsibility. Genuinely asynchronous host operations are configured through
    /// <see cref="RunAsync(Expr, HostOperations, EvaluationLimits?, CancellationToken)"/>
    /// (or <see cref="RunOptions.HostOperations"/> at the engine level), where an
    /// incomplete host awaitable suspends and resumes the run.</para>
    ///
    /// <para>Cancellation follows the synchronous contract exactly — same token, same
    /// chokepoints, same completion-boundary observation — except that, as with any
    /// async API, the <see cref="OperationCanceledException"/> is delivered through the
    /// returned task (which transitions to the Canceled state) rather than thrown
    /// synchronously. The exception instance carries this token; cancellation is never
    /// converted into an <see cref="EvalError"/>.</para>
    /// </summary>
    /// <exception cref="OperationCanceledException">
    /// <paramref name="cancellationToken"/> was cancelled before or during evaluation.
    /// The exception is delivered through the returned task and carries that token.
    /// </exception>
    public static async Task<EvalResult<Result>> RunAsync(
        Expr expr, EvaluationLimits? limits, CancellationToken cancellationToken)
        => await RunAsync(
            expr,
            new RunScopedZeroArgPropertyResultCache(),
            limits,
            loopDiagnostics: null,
            sequenceDiagnostics: null,
            observations: null,
            hostOperations: null,
            cancellationToken).ConfigureAwait(false);

    /// <summary>
    /// Run evaluation with host operations ambiently in scope — the asynchronous
    /// counterpart of <see cref="Run(Expr, HostOperations, EvaluationLimits?, CancellationToken)"/>
    /// and the entry point that accepts ASYNCHRONOUS operations.
    ///
    /// <para>With only synchronous operations configured the run keeps the synchronous
    /// fast path: the returned task completes synchronously on the calling thread, and
    /// behavior is that of the synchronous host-operation overload by identity. With at
    /// least one asynchronous operation the run executes through the async twin path,
    /// and an incomplete <see cref="ValueTask{TResult}"/> returned by an operation
    /// genuinely suspends the evaluation — no thread is blocked, nothing is replayed —
    /// resuming at the same point when the operation completes. Each operation receives
    /// <paramref name="cancellationToken"/>; host exceptions and faulted awaitables
    /// propagate through the returned task unchanged (see <see cref="HostOperation"/>
    /// for the full contract). All parameters are explicit on this overload so existing
    /// <c>RunAsync</c> call sites keep binding exactly as before.</para>
    /// </summary>
    /// <exception cref="OperationCanceledException">
    /// <paramref name="cancellationToken"/> was cancelled before or during evaluation
    /// (including while suspended in a host operation, observed when evaluation
    /// resumes). The exception is delivered through the returned task and carries that
    /// token.
    /// </exception>
    public static async Task<EvalResult<Result>> RunAsync(
        Expr expr,
        HostOperations hostOperations,
        EvaluationLimits? limits,
        CancellationToken cancellationToken)
    {
        ArgumentNullException.ThrowIfNull(hostOperations);
        return await RunAsync(
            expr,
            CreateRunScopedZeroArgPropertyResultCache(hostOperations),
            limits,
            loopDiagnostics: null,
            sequenceDiagnostics: null,
            observations: null,
            hostOperations,
            cancellationToken).ConfigureAwait(false);
    }

    /// <summary>
    /// Asynchronous counterpart of <see cref="RunFlat(Expr)"/>. See
    /// <see cref="RunFlatAsync(Expr, EvaluationLimits?, CancellationToken)"/> for the
    /// contract.
    /// </summary>
    public static Task<EvalResult<IReadOnlyList<Decimal128>>> RunFlatAsync(Expr expr)
        => RunFlatAsync(expr, limits: null);

    /// <summary>
    /// Asynchronous counterpart of <see cref="RunFlat(Expr, EvaluationLimits?)"/>. See
    /// <see cref="RunFlatAsync(Expr, EvaluationLimits?, CancellationToken)"/> for the
    /// contract.
    /// </summary>
    public static Task<EvalResult<IReadOnlyList<Decimal128>>> RunFlatAsync(Expr expr, EvaluationLimits? limits)
        => RunFlatAsync(expr, limits, cancellationToken: default);

    /// <summary>
    /// Asynchronous counterpart of
    /// <see cref="RunFlat(Expr, EvaluationLimits?, CancellationToken)"/>, with the same
    /// synchronous-completion and cancellation notes as
    /// <see cref="RunAsync(Expr, EvaluationLimits?, CancellationToken)"/>.
    /// </summary>
    /// <exception cref="OperationCanceledException">
    /// <paramref name="cancellationToken"/> was cancelled before or during evaluation
    /// or the bounded host projection. The exception is delivered through the returned
    /// task and carries that token.
    /// </exception>
    public static async Task<EvalResult<IReadOnlyList<Decimal128>>> RunFlatAsync(
        Expr expr, EvaluationLimits? limits, CancellationToken cancellationToken)
        => ProjectFlatHostAtoms(
            await RunAsync(expr, limits, cancellationToken).ConfigureAwait(false),
            limits,
            cancellationToken);

    // ── Async entry points (internal) ───────────────────────────────────────

    /// <summary>
    /// The ONE rule that selects the execution family for an async entry point: only a
    /// run component that can complete asynchronously justifies the async twin path.
    /// There are exactly two such components — an async-capable zero-argument property
    /// cache (the internal Phase 2 seam) and a configured ASYNCHRONOUS host operation
    /// (the public Phase 3 surface, which awaits at its wrapper-body site). Everything
    /// else — including a configuration of purely SYNCHRONOUS host operations, whose
    /// delegates complete inline by contract — takes the synchronous pipeline inline:
    /// the honest optimum, since nothing could suspend.
    /// </summary>
    private static bool RequiresAsyncEvaluationPath(
        IZeroArgPropertyResultCache zeroArgPropertyResultCache,
        HostOperations? hostOperations)
        => zeroArgPropertyResultCache is IAsyncZeroArgPropertyResultCache
            || hostOperations?.ContainsAsynchronousOperations == true;

    /// <summary>
    /// Routing enforcement for the twin path's property seam: the twin family awaits
    /// the cache's asynchronous member at every zero-argument property access, and a
    /// synchronous-only cache cannot host that await (its callback would have to be
    /// evaluated eagerly, double-evaluating on hits). A configuration that selects the
    /// twin path through asynchronous host operations must therefore also carry an
    /// async-capable cache; the public entry points construct one, and this guard makes
    /// the requirement fail-loud for internal callers instead of surfacing later as the
    /// twin family's mid-run ownership exception.
    /// </summary>
    private static void ThrowIfAsyncHostOperationsWithoutAsyncCapableCache(
        IZeroArgPropertyResultCache zeroArgPropertyResultCache,
        HostOperations? hostOperations)
    {
        if (hostOperations?.ContainsAsynchronousOperations == true
            && zeroArgPropertyResultCache is not IAsyncZeroArgPropertyResultCache)
        {
            throw new InvalidOperationException(
                "Asynchronous host operations require an async-capable zero-argument property result cache " +
                "for the run; use an async evaluation entry point that constructs one.");
        }
    }

    /// <summary>
    /// The ONE cache-pairing rule for constructing a run's zero-argument property
    /// result cache from its host-operation configuration: a configuration containing
    /// an ASYNCHRONOUS operation routes the run through the async twin path, which
    /// awaits the property seam — so it is paired with the async-capable run-scoped
    /// cache; every other configuration (no host operations, or purely synchronous
    /// ones) keeps the ordinary run-scoped cache and with it the synchronous fast path.
    /// Every call constructs a FRESH cache belonging to one run alone — the pairing
    /// rule never introduces sharing.
    /// <see cref="ThrowIfAsyncHostOperationsWithoutAsyncCapableCache"/> enforces the
    /// same pairing fail-loud for internal callers that supply their own cache.
    /// </summary>
    internal static IZeroArgPropertyResultCache CreateRunScopedZeroArgPropertyResultCache(
        HostOperations? hostOperations)
        => hostOperations?.ContainsAsynchronousOperations == true
            ? new RunScopedAsyncZeroArgPropertyResultCache()
            : new RunScopedZeroArgPropertyResultCache();

    /// <summary>
    /// Run-entry preparation for the ASYNC TWIN family — the twin-path counterpart of
    /// <see cref="PrepareSynchronousRun"/>, sharing the same synchronous
    /// <see cref="PrepareAdmittedRun"/> sequence (nothing in run preparation awaits).
    /// The per-family differences are exactly two and live here: the entry guard is the
    /// cache-pairing ownership check, raised BEFORE the first token observation (an
    /// internal wiring bug fails loud even under a cancelled token), and the root
    /// context pins loop optimization and sequence-pipeline fusion OFF — the twin
    /// family mirrors the generic strategies only, and limit verdicts are
    /// strategy-independent by the budget architecture (see <c>CreateRootCtx</c>), so
    /// this is an internal execution-strategy selection, never a semantic one.
    /// </summary>
    private static PreparedRun PrepareAsyncTwinRun(
        Expr expr,
        IZeroArgPropertyResultCache zeroArgPropertyResultCache,
        LoopOptimizationDiagnostics? loopDiagnostics,
        SequencePipelineDiagnostics? sequenceDiagnostics,
        EvaluationLimits? limits,
        EvaluationObservations? observations,
        HostOperations? hostOperations,
        CancellationToken cancellationToken)
    {
        ThrowIfAsyncHostOperationsWithoutAsyncCapableCache(zeroArgPropertyResultCache, hostOperations);
        cancellationToken.ThrowIfCancellationRequested();

        return PrepareAdmittedRun(
            expr,
            zeroArgPropertyResultCache,
            enableLoopOptimization: false,
            loopDiagnostics,
            enableSequencePipelineOptimization: false,
            sequenceDiagnostics,
            limits,
            observations,
            hostOperations,
            cancellationToken);
    }

    /// <summary>
    /// Internal async run: routes to the synchronous pipeline (fast path) or the async
    /// twin family, per <see cref="RequiresAsyncEvaluationPath"/>. The twin path shares
    /// the internal synchronous
    /// <see cref="Run(Expr, IZeroArgPropertyResultCache, bool, LoopOptimizationDiagnostics?, bool, SequencePipelineDiagnostics?, EvaluationLimits?, EvaluationObservations?, HostOperations?, CancellationToken)"/>
    /// overload's run preparation (through <see cref="PrepareAsyncTwinRun"/>, which pins
    /// the generic strategies — see the class doc) and differs only in its twin dispatch.
    /// </summary>
    internal static async ValueTask<EvalResult<Result>> RunAsync(
        Expr expr,
        IZeroArgPropertyResultCache zeroArgPropertyResultCache,
        EvaluationLimits? limits = null,
        LoopOptimizationDiagnostics? loopDiagnostics = null,
        SequencePipelineDiagnostics? sequenceDiagnostics = null,
        EvaluationObservations? observations = null,
        HostOperations? hostOperations = null,
        CancellationToken cancellationToken = default)
    {
        ArgumentNullException.ThrowIfNull(zeroArgPropertyResultCache);

        if (!RequiresAsyncEvaluationPath(zeroArgPropertyResultCache, hostOperations))
        {
            // Fast path: the synchronous pipeline IS the async result. Same code, same
            // budget accounting, same optimizer eligibility as the sync entry point.
            // Synchronous host operations run here too — their delegates complete
            // inline by contract, so nothing could suspend.
            return Run(
                expr,
                zeroArgPropertyResultCache,
                enableLoopOptimization: true,
                loopDiagnostics,
                enableSequencePipelineOptimization: true,
                sequenceDiagnostics,
                limits,
                observations,
                hostOperations,
                cancellationToken);
        }

        // Twin path: the same shared preparation as the internal synchronous Run(...);
        // only the dispatch below is twin-specific.
        var preparation = PrepareAsyncTwinRun(
            expr, zeroArgPropertyResultCache, loopDiagnostics, sequenceDiagnostics, limits, observations, hostOperations, cancellationToken);
        if (preparation.Error is { } preparationError)
            return preparationError;

        var ctx = preparation.Ctx;
        EvalResult<Result> result;
        if (expr is Expr.AlgorithmExpr(var alg))
        {
            result = await EvalRootProgramValueAsync(alg, expr.Span, ctx).ConfigureAwait(false);
        }
        else
        {
            var countedR = await EvalCountedAsync(expr, ctx, []).ConfigureAwait(false);
            result = countedR.IsError
                ? countedR.Error
                : EvalResult<Result>.Ok(countedR.Value.Value);
        }

        // Completion-boundary observation, exactly as on the synchronous path.
        ctx.Budget.ObserveCancellation();
        return result;
    }

    /// <summary>Async twin of the internal <see cref="RunCounted(Expr, IZeroArgPropertyResultCache, EvaluationLimits?, HostOperations?, CancellationToken)"/>.</summary>
    internal static async ValueTask<EvalResult<CountedResult>> RunCountedAsync(
        Expr expr,
        IZeroArgPropertyResultCache zeroArgPropertyResultCache,
        EvaluationLimits? limits = null,
        HostOperations? hostOperations = null,
        CancellationToken cancellationToken = default)
    {
        ArgumentNullException.ThrowIfNull(zeroArgPropertyResultCache);

        if (!RequiresAsyncEvaluationPath(zeroArgPropertyResultCache, hostOperations))
            return RunCounted(expr, zeroArgPropertyResultCache, limits, hostOperations, cancellationToken);

        // Twin path: the same shared preparation as RunCounted; only the dispatch
        // below is twin-specific.
        var preparation = PrepareAsyncTwinRun(
            expr, zeroArgPropertyResultCache, loopDiagnostics: null, sequenceDiagnostics: null, limits, observations: null, hostOperations, cancellationToken);
        if (preparation.Error is { } preparationError)
            return preparationError;

        var ctx = preparation.Ctx;
        var result = expr is Expr.AlgorithmExpr(var alg)
            ? await EvalRootProgramCountedAsync(alg, expr.Span, ctx).ConfigureAwait(false)
            : await EvalCountedAsync(expr, ctx, []).ConfigureAwait(false);

        ctx.Budget.ObserveCancellation();
        return result;
    }

    /// <summary>Async twin of the internal <see cref="RunCountedWithTopLevelProperty"/>.</summary>
    internal static async ValueTask<EvalResult<CountedRootProgramResult>> RunCountedWithTopLevelPropertyAsync(
        Expr expr,
        string topLevelPropertyName,
        IZeroArgPropertyResultCache zeroArgPropertyResultCache,
        EvaluationLimits? limits = null,
        HostOperations? hostOperations = null,
        CancellationToken cancellationToken = default)
    {
        ArgumentNullException.ThrowIfNull(zeroArgPropertyResultCache);
        ArgumentException.ThrowIfNullOrWhiteSpace(topLevelPropertyName);

        if (!RequiresAsyncEvaluationPath(zeroArgPropertyResultCache, hostOperations))
            return RunCountedWithTopLevelProperty(expr, topLevelPropertyName, zeroArgPropertyResultCache, limits, hostOperations, cancellationToken);

        // Twin path: the same shared preparation as RunCountedWithTopLevelProperty;
        // only the dispatch below is twin-specific.
        var preparation = PrepareAsyncTwinRun(
            expr, zeroArgPropertyResultCache, loopDiagnostics: null, sequenceDiagnostics: null, limits, observations: null, hostOperations, cancellationToken);
        if (preparation.Error is { } preparationError)
            return preparationError;

        var ctx = preparation.Ctx;
        EvalResult<CountedRootProgramResult> result;
        if (expr is Expr.AlgorithmExpr(var alg))
        {
            result = await EvalRootProgramCountedWithTopLevelPropertyAsync(alg, expr.Span, ctx, topLevelPropertyName)
                .ConfigureAwait(false);
        }
        else
        {
            var outputR = await EvalCountedAsync(expr, ctx, []).ConfigureAwait(false);
            result = outputR.IsError
                ? outputR.Error
                : EvalResult<CountedRootProgramResult>.Ok(
                    new CountedRootProgramResult(outputR.Value, TopLevelProperty: null));
        }

        ctx.Budget.ObserveCancellation();
        return result;
    }

    /// <summary>
    /// Async twin of the <see cref="RunCountedObserved"/> harness entry point: same
    /// budget hand-back so async tests can compare the OPERATIONAL counters a twin-path
    /// run actually charged against a synchronous baseline.
    /// </summary>
    internal static async ValueTask<(EvalResult<CountedResult> Result, EvaluationBudget Budget)> RunCountedObservedAsync(
        Expr expr,
        EvaluationLimits? limits = null,
        IZeroArgPropertyResultCache? zeroArgPropertyResultCache = null,
        LoopOptimizationDiagnostics? loopDiagnostics = null,
        SequencePipelineDiagnostics? sequenceDiagnostics = null,
        EvaluationObservations? observations = null,
        HostOperations? hostOperations = null,
        CancellationToken cancellationToken = default)
    {
        var cache = zeroArgPropertyResultCache
            ?? CreateRunScopedZeroArgPropertyResultCache(hostOperations);
        if (!RequiresAsyncEvaluationPath(cache, hostOperations))
        {
            return RunCountedObserved(
                expr,
                limits,
                enableOptimizations: true,
                cache,
                loopDiagnostics,
                sequenceDiagnostics,
                observations,
                hostOperations,
                cancellationToken);
        }

        // Twin path: the same shared preparation as RunCountedObserved; only the
        // dispatch below is twin-specific.
        var preparation = PrepareAsyncTwinRun(
            expr, cache, loopDiagnostics, sequenceDiagnostics, limits, observations, hostOperations, cancellationToken);
        if (preparation.Error is { } preparationError)
            return (preparationError, preparation.Budget);

        var ctx = preparation.Ctx;
        var result = expr is Expr.AlgorithmExpr(var alg)
            ? await EvalRootProgramCountedAsync(alg, expr.Span, ctx).ConfigureAwait(false)
            : await EvalCountedAsync(expr, ctx, []).ConfigureAwait(false);

        ctx.Budget.ObserveCancellation();
        return (result, ctx.Budget);
    }

    // ── Root program twins ──────────────────────────────────────────────────

    /// <summary>
    /// MIRROR OF <see cref="EvalRootProgram"/> — keep in lock-step. The value is the
    /// counted program output's value (the synchronous plain path is exactly that
    /// projection: <c>EvalProgramOutput → EvalAlgOutputCore → EvalAlgOutputCountedCore</c>).
    /// </summary>
    private static async ValueTask<EvalResult<Result>> EvalRootProgramValueAsync(Algorithm alg, SourceSpan? span, EvalCtx ctx)
    {
        var wired = WireToCaller(ctx, alg);
        if (wired.Params.Count == 0)
        {
            var countedR = await EvalAlgOutputCountedCoreAsync(wired, ctx, []).ConfigureAwait(false);
            var result = countedR.IsError
                ? countedR.Error
                : EvalResult<Result>.Ok(countedR.Value.Value);
            if (result.IsError
                && result.Error is EvalError.MissingOutput
                && wired is Algorithm.User { Output.Count: 0 })
            {
                return new EvalError.WithContext(new ProgramEvaluationContext(), result.Error)
                {
                    Span = result.Error.Span ?? span,
                };
            }

            return result;
        }

        var blockSpan = span ?? FirstSpan(wired.Output);
        return MissingImplicitArguments<Result>(wired, blockSpan);
    }

    /// <summary>MIRROR OF <see cref="EvalRootProgramCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalRootProgramCountedAsync(Algorithm alg, SourceSpan? span, EvalCtx ctx)
    {
        var wired = WireToCaller(ctx, alg);
        if (wired.Params.Count == 0)
        {
            var result = await EvalAlgOutputCountedCoreAsync(wired, ctx, []).ConfigureAwait(false);
            if (result.IsError
                && result.Error is EvalError.MissingOutput
                && wired is Algorithm.User { Output.Count: 0 })
            {
                return new EvalError.WithContext(new ProgramEvaluationContext(), result.Error)
                {
                    Span = result.Error.Span ?? span,
                };
            }

            return result;
        }

        var blockSpan = span ?? FirstSpan(wired.Output);
        return MissingImplicitArguments<CountedResult>(wired, blockSpan);
    }

    /// <summary>MIRROR OF <see cref="EvalRootProgramCountedWithTopLevelProperty"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedRootProgramResult>> EvalRootProgramCountedWithTopLevelPropertyAsync(
        Algorithm alg,
        SourceSpan? span,
        EvalCtx ctx,
        string topLevelPropertyName)
    {
        var wired = WireToCaller(ctx, alg);
        if (wired.Params.Count != 0)
        {
            var blockSpan = span ?? FirstSpan(wired.Output);
            return MissingImplicitArguments<CountedRootProgramResult>(wired, blockSpan);
        }

        var outputR = await EvalAlgOutputCountedCoreAsync(wired, ctx, []).ConfigureAwait(false);
        if (outputR.IsError)
        {
            if (outputR.Error is EvalError.MissingOutput
                && wired is Algorithm.User { Output.Count: 0 })
            {
                return new EvalError.WithContext(new ProgramEvaluationContext(), outputR.Error)
                {
                    Span = outputR.Error.Span ?? span,
                };
            }

            return outputR.Error;
        }

        var propertyR = await EvalTopLevelZeroArgPropertyCountedAsync(wired, topLevelPropertyName, ctx, []).ConfigureAwait(false);
        return propertyR.IsError
            ? propertyR.Error
            : EvalResult<CountedRootProgramResult>.Ok(new CountedRootProgramResult(outputR.Value, propertyR.Value));
    }

    /// <summary>MIRROR OF <see cref="EvalTopLevelZeroArgPropertyCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult?>> EvalTopLevelZeroArgPropertyCountedAsync(
        Algorithm alg,
        string name,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var binding = LookupPropBinding(alg, name);
        if (binding is null)
            return EvalResult<CountedResult?>.Ok(null);

        var resolvedAlgorithm = ChildOf(alg, binding.Value);
        var span = binding.DeclarationSpans.FirstOrDefault();
        if (resolvedAlgorithm.Params.Count != 0)
        {
            return WithSpan<CountedResult?>(
                span,
                new EvalError.WithContext(
                    CtxProperty(name),
                    ZeroArgumentDemandArityMismatch(resolvedAlgorithm)));
        }

        var propertyR = WithPropertyContextOnMissingOutput(
            name,
            span,
            await EvalZeroArgPropertyAccessCountedAsync(
                new ResolvedLexicalProperty(alg, binding, resolvedAlgorithm),
                ctx,
                valEnv).ConfigureAwait(false));

        return propertyR.IsError
            ? propertyR.Error
            : EvalResult<CountedResult?>.Ok(propertyR.Value);
    }

    // ── Main dispatch twin ──────────────────────────────────────────────────

    /// <summary>
    /// MIRROR OF <see cref="EvalCounted"/> — keep in lock-step, case for case.
    /// Cases whose synchronous counterpart delegated to the PLAIN evaluator award the
    /// counted twin's value projection instead; each such case notes the substitution.
    /// </summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalCountedAsync(
        Expr expr,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        // Bulk pathological-work bound — identical charging to the synchronous dispatch heads.
        if (ctx.Budget.TryChargeExpressionNodeWork() is { } nodeWorkError)
            return nodeWorkError;

        switch (expr)
        {
            case Expr.Param(var name):
                {
                    var counted = LookupCountedParam(ctx.CountedParamEnv, name);
                    if (counted is not null)
                        return EvalResult<CountedResult>.Ok(counted.Value);

                    var val = LookupVal(valEnv, name);
                    if (val is not null)
                        return EvalResult<CountedResult>.Ok(new CountedResult(val, val.ValueCount()));

                    var algBinding = LookupAlgBinding(ctx.AlgEnv, name);
                    if (algBinding is { } bound)
                    {
                        if (bound.ValueError is { } stickyLimit)
                            return AtSpanIfMissing(stickyLimit, expr.Span);
                        var algBound = bound.Algorithm;
                        if (ConditionalValueAccessError(name, algBound) is { } conditionalError)
                            return conditionalError with { Span = expr.Span };
                        if (algBound.Params.Count == 0)
                        {
                            var valueR = WithSpan(
                                expr.Span,
                                await EvalResolvedAlgOutputForValueDemandAsync(algBound, ctx, valEnv).ConfigureAwait(false));
                            return valueR.IsError
                                ? valueR.Error
                                : EvalResult<CountedResult>.Ok(new CountedResult(valueR.Value, valueR.Value.ValueCount()));
                        }
                        return ZeroArgumentDemandArityMismatch(algBound) with { Span = expr.Span };
                    }

                    return new EvalError.UnknownName(name) { Span = expr.Span };
                }

            case Expr.SequenceSpread:
                return await EvalSequenceSpreadCountedAsync(expr, ctx, valEnv).ConfigureAwait(false);

            case Expr.SequenceConstruct:
                return await EvalSequenceConstructCountedAsync(expr, ctx, valEnv).ConfigureAwait(false);

            case Expr.Unary or Expr.Binary or Expr.ListLiteral:
                return await EvalExpressionSpineCountedAsync(expr, ctx, valEnv).ConfigureAwait(false);

            case Expr.EmptySequence(var depth):
                {
                    var emptyValue = BuildEmptySequenceValue(depth);
                    return EvalResult<CountedResult>.Ok(new CountedResult(emptyValue, emptyValue.ValueCount()));
                }

            case Expr.AlgorithmExpr(var alg):
                {
                    // Sync counted case calls the plain EvalAlgOutput; the twin awaits the
                    // counted core and projects its value (the plain wrapper is that projection).
                    var wired = WireToCaller(ctx, alg);
                    if (wired.Params.Count == 0)
                    {
                        var blockR = WithSpan(
                            PreferExpressionSpan(expr.Span, wired.Output),
                            await EvalAlgOutputValueAsync(wired, ctx, valEnv).ConfigureAwait(false));
                        if (blockR.IsError) return blockR.Error;
                        return EvalResult<CountedResult>.Ok(new CountedResult(blockR.Value, blockR.Value.ValueCount()));
                    }

                    var blockSpan = PreferExpressionSpan(expr.Span, wired.Output);
                    return MissingImplicitArguments<CountedResult>(wired, blockSpan);
                }

            case Expr.Capture(var captureBody):
                {
                    var captureR = WithSpan(
                        PreferExpressionSpan(expr.Span, captureBody),
                        await EvalCaptureValueAsync(captureBody, ctx, valEnv).ConfigureAwait(false));
                    if (captureR.IsError) return captureR.Error;
                    return EvalResult<CountedResult>.Ok(new CountedResult(captureR.Value, captureR.Value.ValueCount()));
                }

            case Expr.Resolve(var name):
                {
                    if (ctx.CallStack.Count == 0)
                        return new EvalError.UnknownName(name) { Span = expr.Span };

                    var resolvedR = LookupLexical(ctx.CallStack[0], name, ctx);
                    if (resolvedR.IsError)
                        return AtSpanIfMissing(resolvedR.Error, expr.Span);

                    if (ConditionalValueAccessError(name, resolvedR.Value.ResolvedAlgorithm) is { } conditionalError)
                        return conditionalError with { Span = expr.Span };

                    if (resolvedR.Value.ResolvedAlgorithm.Params.Count != 0)
                    {
                        return WithSpan<CountedResult>(
                            expr.Span,
                            new EvalError.WithContext(
                                CtxProperty(name),
                                ZeroArgumentDemandArityMismatch(resolvedR.Value.ResolvedAlgorithm)));
                    }

                    var propertyR = WithPropertyContextOnMissingOutput(name, expr.Span,
                        await EvalZeroArgPropertyAccessCountedAsync(resolvedR.Value, ctx, valEnv).ConfigureAwait(false));
                    return propertyR.IsError
                        ? propertyR.Error
                        : EvalResult<CountedResult>.Ok(new CountedResult(
                            propertyR.Value.Value,
                            propertyR.Value.Value.ValueCount()));
                }

            case Expr.DotCall dotCallExpr:
                return WithSpan(expr.Span, WithDotCallCtx(dotCallExpr, ctx,
                    await EvalDotCallCountedAsync(dotCallExpr, ctx, valEnv).ConfigureAwait(false)));

            case Expr.Call(var func, var callArgs):
                return WithSpan(expr.Span,
                    await EvalCallCountedExprAsync(func, callArgs, ctx, valEnv).ConfigureAwait(false));

            case Expr.Index:
                return await EvalExpressionSpineCountedAsync(expr, ctx, valEnv).ConfigureAwait(false);

            case Expr.NativeCall(var nativeFnName, var nativeArgNames)
                when ctx.Budget.HostOperations is { } hostOperations
                    && nativeFnName.StartsWith(HostOperations.NativeNamePrefix, StringComparison.Ordinal)
                    && hostOperations.TryGetByNativeName(nativeFnName, out var hostOperation)
                    && hostOperation.IsAsynchronous:
                // THE Phase 3 await site: an ASYNCHRONOUS host operation completes by
                // suspending the spine here. Synchronous host operations and built-in
                // Math natives stay leaves of the default case below — their dispatch
                // completes inline in the shared synchronous EvalNativeCall.
                return await EvalAsynchronousHostOperationCountedAsync(
                    hostOperation, nativeArgNames, ctx, valEnv).ConfigureAwait(false);

            // SYNC-DELEGABLE LEAVES — the only kinds allowed to run through
            // the synchronous evaluator on the twin path: none evaluates a
            // child expression, so delegating to the synchronous Eval here is
            // exact — the same leaf code the synchronous counted dispatch
            // runs. Grace is the illegal-in-eval catch-all (a structured
            // error, no child evaluation). A NativeCall naming an
            // ASYNCHRONOUS host operation is the one NativeCall that is not a
            // synchronous leaf; it is intercepted by the guarded case above
            // and never reaches this delegation. Keep this classification in
            // lock-step with EvalCounted.
            case Expr.Num:
            case Expr.StringLiteral:
            case Expr.NativeCall:
            case Expr.Grace:
                {
                    var resultR = Eval(expr, ctx, valEnv);
                    if (resultR.IsError) return resultR.Error;
                    return EvalResult<CountedResult>.Ok(new CountedResult(resultR.Value, resultR.Value.ValueCount()));
                }

            // Exhaustiveness guard, matching AstWalker.VisitExpr: a new Expr
            // variant must be classified above — an explicit twin case, or a
            // proven non-recursive leaf added to the delegation group — so a
            // recursive variant can never silently bypass the async twin
            // family by evaluating its children synchronously.
            default:
                throw new InvalidOperationException(
                    $"Unhandled Expr variant in {nameof(Evaluator)}.{nameof(EvalCountedAsync)}: {expr.GetType().Name}. " +
                    "Add an explicit async twin case (or classify it as a proven leaf) here and in EvalCounted.");
        }
    }

    // ── Expression-spine machine twin ───────────────────────────────────────

    /// <summary>
    /// MIRROR OF <see cref="EvalExpressionSpineCounted"/> — keep in lock-step.
    /// The machine stays ITERATIVE (one explicit frame stack, O(1) CLR stack per spine
    /// node, one async state machine for the whole spine); only its delegated non-spine
    /// children are awaited. Two mechanical differences from the synchronous text, both
    /// forced by <c>await</c>:
    /// <list type="bullet">
    ///   <item>frames are addressed by INDEX (<c>frames[top].X</c> element access)
    ///   instead of a <c>ref</c> local, because a <c>ref</c> local may not live across an
    ///   await; array element access mutates in place identically;</item>
    ///   <item>delegated children go through the counted twin and project the value the
    ///   synchronous machine obtained from plain <see cref="Eval"/> (the plain result is
    ///   that projection).</item>
    /// </list>
    /// </summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalExpressionSpineCountedAsync(
        Expr root,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var frames = new ExpressionSpineFrame[16];
        var frameCount = 0;
        frames[frameCount++] = new ExpressionSpineFrame(root);

        CountedResult pendingChild = default;
        var hasPendingChild = false;

        while (true)
        {
            // Bulk pathological-work bound: each frame transition contributes to the
            // same cheap bulk-work counter as the synchronous machine.
            if (ctx.Budget.TryChargeExpressionNodeWork() is { } nodeWorkError)
                return nodeWorkError;

            var top = frameCount - 1;
            EvalResult<CountedResult>? completed = null;
            Expr? requestedChild = null;

            switch (frames[top].Node)
            {
                case Expr.Unary(var unaryOp, var operand):
                    {
                        if (!hasPendingChild)
                        {
                            requestedChild = operand;
                            break;
                        }

                        hasPendingChild = false;
                        var unaryR = ApplyUnaryOperator(unaryOp, pendingChild.Value, frames[top].Node.Span);
                        completed = unaryR.IsError
                            ? unaryR.Error
                            : EvalResult<CountedResult>.Ok(new CountedResult(
                                unaryR.Value, unaryR.Value.ValueCount()));
                        break;
                    }

                case Expr.Binary(var op, var left, var right):
                    {
                        if (frames[top].Phase == 0)
                        {
                            if (!hasPendingChild)
                            {
                                requestedChild = left;
                                break;
                            }

                            hasPendingChild = false;
                            frames[top].FirstValue = pendingChild.Value;
                            frames[top].Phase = 1;
                            requestedChild = right;
                            break;
                        }

                        hasPendingChild = false;
                        var binaryR = ApplyBinaryOperator(
                            op, left, right, frames[top].FirstValue!, pendingChild.Value, frames[top].Node.Span);
                        completed = binaryR.IsError
                            ? binaryR.Error
                            : EvalResult<CountedResult>.Ok(new CountedResult(
                                binaryR.Value, binaryR.Value.ValueCount()));
                        break;
                    }

                case Expr.Index(var target, var selector):
                    {
                        if (frames[top].Phase == 0)
                        {
                            if (!hasPendingChild)
                            {
                                requestedChild = target;
                                break;
                            }

                            hasPendingChild = false;
                            frames[top].FirstValue = pendingChild.Value;
                            frames[top].Phase = 1;
                            requestedChild = selector;
                            break;
                        }

                        hasPendingChild = false;

                        var nR = ExpectInt(pendingChild.Value);
                        if (nR.IsError)
                        {
                            completed = AtSpanIfMissing(nR.Error, frames[top].Node.Span);
                            break;
                        }

                        var n = nR.Value;
                        // IsInteger is false for NaN and the infinities, so a non-finite
                        // selector is the same out-of-range badIndex as a fractional one.
                        if (!Decimal128.IsInteger(n) || n < 0)
                        {
                            completed = new EvalError.BadIndex() { Span = frames[top].Node.Span };
                            break;
                        }

                        if (n > int.MaxValue)
                        {
                            completed = new EvalError.BadIndex() { Span = frames[top].Node.Span };
                            break;
                        }

                        var selected = frames[top].FirstValue!.SelectProjected((int)n);
                        completed = selected is null
                            ? new EvalError.BadIndex() { Span = frames[top].Node.Span }
                            : EvalResult<CountedResult>.Ok(new CountedResult(
                                selected.Value.Value, selected.Value.EmittedCount));
                        break;
                    }

                case Expr.ListLiteral(var elements):
                    {
                        frames[top].ListItems ??= [];
                        if (hasPendingChild)
                        {
                            // WRITTEN-SLOT REIFICATION: a machine-kind element is never a
                            // spread, so its counted supply contributes exactly ONE value.
                            hasPendingChild = false;
                            frames[top].ListItems!.Add(pendingChild.Value);
                            frames[top].Phase++;
                        }

                        while (frames[top].Phase < elements.Count)
                        {
                            var element = elements[frames[top].Phase];
                            if (IsExpressionSpineNode(element))
                                break;

                            var slotsR = await EvalExplicitSequenceValueExprSlotsAsync(element, ctx, valEnv).ConfigureAwait(false);
                            if (slotsR.IsError)
                            {
                                completed = slotsR.Error;
                                break;
                            }

                            frames[top].ListItems!.AddRange(slotsR.Value);
                            frames[top].Phase++;
                        }

                        if (completed is not null)
                            break;

                        if (frames[top].Phase < elements.Count)
                        {
                            requestedChild = elements[frames[top].Phase];
                            break;
                        }

                        // Cardinality is known once the written slots (including spread
                        // expansion) are evaluated, so the reservation happens before the
                        // persistent list is built.
                        if (ReserveCollection(ctx, frames[top].ListItems!.Count, frames[top].Node.Span) is { } limitError)
                        {
                            completed = limitError;
                            break;
                        }

                        completed = EvalResult<CountedResult>.Ok(new CountedResult(
                            Result.ListValue.TakeOwnership(frames[top].ListItems!.ToArray()), 1));
                        break;
                    }

                default:
                    throw new InvalidOperationException(
                        $"EvalExpressionSpineCountedAsync received the non-spine node kind '{frames[top].Node.GetType()}'.");
            }

            if (requestedChild is not null)
            {
                if (IsExpressionSpineNode(requestedChild))
                {
                    if (frameCount == frames.Length)
                        Array.Resize(ref frames, frames.Length * 2);
                    frames[frameCount++] = new ExpressionSpineFrame(requestedChild);
                    continue;
                }

                // Delegated child: the synchronous machine calls plain Eval here; the
                // twin awaits the counted dispatch and projects the same value.
                var childR = await EvalCountedAsync(requestedChild, ctx, valEnv).ConfigureAwait(false);
                if (childR.IsError)
                {
                    completed = childR.Error;
                }
                else
                {
                    pendingChild = new CountedResult(childR.Value.Value, childR.Value.Value.ValueCount());
                    hasPendingChild = true;
                    continue;
                }
            }

            if (completed is not { } completedResult)
                continue;

            if (completedResult.IsError)
            {
                // Unwind exactly like the recursive returns — see the synchronous machine.
                var error = completedResult.Error;
                var decorateTopFrame = requestedChild is not null;
                while (frameCount > 0)
                {
                    if (decorateTopFrame && frames[frameCount - 1].Node is Expr.Index)
                        error = AtSpanIfMissing(error, frames[frameCount - 1].Node.Span);

                    decorateTopFrame = true;
                    frameCount--;
                }

                return error;
            }

            frameCount--;
            if (frameCount == 0)
                return completedResult;

            pendingChild = completedResult.Value;
            hasPendingChild = true;
        }
    }

    // ── Algorithm output / capture twins ────────────────────────────────────

    /// <summary>MIRROR OF <see cref="EvalAlgOutputPreparedCore"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<PreparedAlgorithmOutput>> EvalAlgOutputPreparedCoreAsync(
        Algorithm alg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (alg is Algorithm.Builtin(var builtin))
        {
            var countedR = EvalBuiltinValueCounted(builtin);
            return countedR.IsError
                ? countedR.Error
                : EvalResult<PreparedAlgorithmOutput>.Ok(new(
                    countedR.Value,
                    CountedTopLevelValues(countedR.Value)));
        }

        var dupProp = alg.FindDuplicatePropName();
        if (dupProp is not null)
            return new EvalError.DuplicateProperty(dupProp);

        if (ConditionalValueAccessError("conditional", alg) is { } conditionalError)
            return conditionalError;

        if (alg is Algorithm.User { Output: { Count: 0 } })
            return new EvalError.MissingOutput();

        return await EvalOutputRowsPreparedCoreAsync(alg.Output, ctx.Push(alg), ctx, valEnv).ConfigureAwait(false);
    }

    /// <summary>
    /// MIRROR OF <see cref="EvalOutputRowsPreparedCore"/> — keep in lock-step, except
    /// for the twin-only STRUCTURAL-NESTING STACK BACKSTOP at the head: nested
    /// algorithm/capture bodies recurse through async state-machine frames that are
    /// larger than their synchronous counterparts, and this chain passes no invocation
    /// chokepoint (structural nesting charges no dynamic depth), so the synchronous
    /// family's shape calibration does not transfer. The probe converts an outgrowing
    /// chain into the established structured error; like the invocation-chokepoint
    /// probe it can only stop evaluation EARLIER than a physical overflow, never change
    /// a run that has host stack headroom, and it moves no budget counter.
    /// </summary>
    private static async ValueTask<EvalResult<PreparedAlgorithmOutput>> EvalOutputRowsPreparedCoreAsync(
        IReadOnlyList<Expr> rows,
        EvalCtx rowCtx,
        EvalCtx reserveCtx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (!RuntimeHelpers.TryEnsureSufficientExecutionStack())
            return new EvalError.EvaluationStackExhausted();

        var results = new List<Result>();
        var emittedCount = 0;

        foreach (var expr in rows)
        {
            var countedR = await EvalCountedAsync(expr, rowCtx, valEnv).ConfigureAwait(false);
            if (countedR.IsError) return countedR.Error;

            if (expr is Expr.SequenceSpread)
            {
                AddCountedTopLevelValues(results, countedR.Value);
                emittedCount += countedR.Value.EmittedCount;
                continue;
            }

            // A non-spread output expression is always one visible output slot,
            // even when it evaluates to the empty sequence value `()`.
            results.Add(countedR.Value.Value);
            emittedCount += countedR.Value.EmittedCount == 0 ? 1 : countedR.Value.EmittedCount;
        }

        if (ReserveSequenceCapture(reserveCtx, results.Count, FirstSpan(rows)) is { } capturedLimitError)
            return capturedLimitError;

        var counted = new CountedResult(CombineOutputSlots(results), emittedCount);
        return EvalResult<PreparedAlgorithmOutput>.Ok(new(counted, results));
    }

    /// <summary>MIRROR OF <see cref="EvalCapturePreparedCore"/> — keep in lock-step.</summary>
    private static ValueTask<EvalResult<PreparedAlgorithmOutput>> EvalCapturePreparedCoreAsync(
        OutputBundle body,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
        => EvalOutputRowsPreparedCoreAsync(body, ctx, ctx, valEnv);

    /// <summary>MIRROR OF <see cref="EvalCaptureCountedCore"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalCaptureCountedCoreAsync(
        OutputBundle body,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var preparedR = await EvalCapturePreparedCoreAsync(body, ctx, valEnv).ConfigureAwait(false);
        return preparedR.IsError
            ? preparedR.Error
            : EvalResult<CountedResult>.Ok(preparedR.Value.Counted);
    }

    /// <summary>MIRROR OF <see cref="EvalCaptureValue"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<Result>> EvalCaptureValueAsync(
        OutputBundle body,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var countedR = await EvalCaptureCountedCoreAsync(body, ctx, valEnv).ConfigureAwait(false);
        return countedR.IsError
            ? countedR.Error
            : EvalResult<Result>.Ok(countedR.Value.Value);
    }

    /// <summary>MIRROR OF <see cref="EvalAlgOutputCountedCore"/> / <see cref="EvalAlgOutputCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalAlgOutputCountedCoreAsync(
        Algorithm alg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var preparedR = await EvalAlgOutputPreparedCoreAsync(alg, ctx, valEnv).ConfigureAwait(false);
        return preparedR.IsError
            ? preparedR.Error
            : EvalResult<CountedResult>.Ok(preparedR.Value.Counted);
    }

    /// <summary>
    /// MIRROR OF <see cref="EvalAlgOutputCore"/> / <see cref="EvalAlgOutput"/> — keep in
    /// lock-step. The synchronous wrapper projects <see cref="EvalAlgOutputCountedCore"/>;
    /// this async twin projects the identical counted field from the shared prepared core
    /// directly, avoiding a redundant async wrapper without owning any semantics.
    /// </summary>
    private static async ValueTask<EvalResult<Result>> EvalAlgOutputValueAsync(
        Algorithm alg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var preparedR = await EvalAlgOutputPreparedCoreAsync(alg, ctx, valEnv).ConfigureAwait(false);
        return preparedR.IsError
            ? preparedR.Error
            : EvalResult<Result>.Ok(preparedR.Value.Counted.Value);
    }

    /// <summary>MIRROR OF <see cref="EvalAlgOutputSlots"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<IReadOnlyList<Result>>> EvalAlgOutputSlotsAsync(
        Algorithm alg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        bool preserveSequenceSpreadExpressionBoundaries = false)
    {
        if (alg is Algorithm.Builtin(var builtin))
        {
            var countedR = EvalBuiltinValueCounted(builtin);
            return countedR.IsError
                ? countedR.Error
                : EvalResult<IReadOnlyList<Result>>.Ok(CountedTopLevelValues(countedR.Value));
        }

        if (alg.FindDuplicatePropName() is { } duplicateName)
            return new EvalError.DuplicateProperty(duplicateName);

        if (ConditionalValueAccessError("conditional", alg) is { } conditionalError)
            return conditionalError;

        if (alg is Algorithm.User { Output.Count: 0 })
            return new EvalError.MissingOutput();

        var slots = new List<Result>();
        var pushedCtx = ctx.Push(alg);
        foreach (var expr in alg.Output)
        {
            var countedR = await EvalCountedAsync(expr, pushedCtx, valEnv).ConfigureAwait(false);
            if (countedR.IsError) return countedR.Error;

            if (preserveSequenceSpreadExpressionBoundaries && expr is Expr.SequenceSpread)
            {
                if (countedR.Value.EmittedCount != 0)
                    slots.Add(countedR.Value.Value);
                continue;
            }

            if (expr is Expr.SequenceSpread || countedR.Value.EmittedCount != 0)
                slots.AddRange(CountedTopLevelValues(countedR.Value));
            else
                slots.Add(countedR.Value.Value);
        }

        return EvalResult<IReadOnlyList<Result>>.Ok(slots);
    }

    // ── Explicit written-slot twins ─────────────────────────────────────────

    /// <summary>MIRROR OF <see cref="EvalExplicitSequenceValueItems"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<IReadOnlyList<Result>>> EvalExplicitSequenceValueItemsAsync(
        Algorithm alg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (alg is Algorithm.Builtin(var builtin))
        {
            var countedR = EvalBuiltinValueCounted(builtin);
            return countedR.IsError
                ? countedR.Error
                : EvalResult<IReadOnlyList<Result>>.Ok(CountedTopLevelValues(countedR.Value));
        }

        if (alg.FindDuplicatePropName() is { } duplicateName)
            return new EvalError.DuplicateProperty(duplicateName);

        if (ConditionalValueAccessError("conditional", alg) is { } conditionalError)
            return conditionalError;

        if (alg is Algorithm.User { Output.Count: 0 })
            return new EvalError.MissingOutput();

        return await EvalExplicitSequenceValueRowSlotsAsync(alg.Output, ctx.Push(alg), valEnv).ConfigureAwait(false);
    }

    /// <summary>
    /// MIRROR OF <see cref="EvalExplicitSequenceValueRowSlots"/> — keep in lock-step,
    /// plus the twin-only structural-nesting stack backstop (see
    /// <see cref="EvalOutputRowsPreparedCoreAsync"/>): nested written groups recurse
    /// through this family without touching the ordinary dispatch or any invocation
    /// chokepoint.
    /// </summary>
    private static async ValueTask<EvalResult<IReadOnlyList<Result>>> EvalExplicitSequenceValueRowSlotsAsync(
        IReadOnlyList<Expr> rows,
        EvalCtx rowCtx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (!RuntimeHelpers.TryEnsureSufficientExecutionStack())
            return new EvalError.EvaluationStackExhausted();

        var slots = new List<Result>();
        foreach (var expr in rows)
        {
            var exprSlotsR = await EvalExplicitSequenceValueExprSlotsAsync(expr, rowCtx, valEnv).ConfigureAwait(false);
            if (exprSlotsR.IsError) return exprSlotsR.Error;
            slots.AddRange(exprSlotsR.Value);
        }

        return EvalResult<IReadOnlyList<Result>>.Ok(slots);
    }

    /// <summary>MIRROR OF <see cref="EvalExplicitSequenceValueExprSlots"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<IReadOnlyList<Result>>> EvalExplicitSequenceValueExprSlotsAsync(
        Expr expr,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (expr is Expr.Capture(var captureBody))
        {
            var nestedItemsR = await EvalExplicitSequenceValueRowSlotsAsync(captureBody, ctx, valEnv).ConfigureAwait(false);
            if (nestedItemsR.IsError) return nestedItemsR.Error;

            return EvalResult<IReadOnlyList<Result>>.Ok([CombineOutputSlots(nestedItemsR.Value)]);
        }

        if (expr is Expr.AlgorithmExpr(var algorithm))
        {
            var wired = WireToCaller(ctx, algorithm);
            if (wired.Params.Count == 0)
            {
                var nestedItemsR = await EvalExplicitSequenceValueItemsAsync(wired, ctx, valEnv).ConfigureAwait(false);
                if (nestedItemsR.IsError) return nestedItemsR.Error;

                return EvalResult<IReadOnlyList<Result>>.Ok([CombineOutputSlots(nestedItemsR.Value)]);
            }
        }

        var countedR = await EvalCountedAsync(expr, ctx, valEnv).ConfigureAwait(false);
        if (countedR.IsError) return countedR.Error;

        // WRITTEN-SLOT REIFICATION — see the synchronous twin.
        return expr is Expr.SequenceSpread
            ? EvalResult<IReadOnlyList<Result>>.Ok(CountedTopLevelValues(countedR.Value))
            : EvalResult<IReadOnlyList<Result>>.Ok([countedR.Value.Value]);
    }

    // ── Zero-argument property twins (the async host seam) ──────────────────

    /// <summary>MIRROR OF <see cref="EvaluateZeroArgPropertyResult"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<ZeroArgPropertyResult>> EvaluateZeroArgPropertyResultAsync(
        Algorithm resolvedAlgorithm,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var countedR = await EvalAlgOutputCountedCoreAsync(resolvedAlgorithm, ctx, valEnv).ConfigureAwait(false);
        if (countedR.IsError)
            return countedR.Error;

        return EvalResult<ZeroArgPropertyResult>.Ok(
            new ZeroArgPropertyResult(countedR.Value.Value, countedR.Value.EmittedCount));
    }

    /// <summary>MIRROR OF <see cref="GetOrEvaluateZeroArgPropertyResult"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<ZeroArgPropertyResult>> GetOrEvaluateZeroArgPropertyResultAsync(
        Algorithm? owner,
        Property binding,
        ZeroArgPropertyAccessKind accessKind,
        Algorithm resolvedAlgorithm,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        // Charged dynamic invocation boundary, entered BEFORE the cache is consulted —
        // identical protocol to the synchronous twin, released from the finally on every
        // completion path including exceptional unwind through a suspended seam await.
        if (ctx.Budget.TryEnterInvocation() is { } limitError)
            return AtSpanIfMissing(limitError, binding.DeclarationSpans.FirstOrDefault());

        try
        {
            return await GetOrEvaluateZeroArgPropertyResultCoreAsync(
                owner, binding, accessKind, resolvedAlgorithm, ctx, valEnv).ConfigureAwait(false);
        }
        finally
        {
            ctx.Budget.ExitInvocation();
        }
    }

    /// <summary>
    /// MIRROR OF <see cref="GetOrEvaluateZeroArgPropertyResultCore"/> — keep in lock-step.
    /// This is the async PROPERTY-CACHE seam. Phase 3's public asynchronous host
    /// operations have their separate, single await site in
    /// <see cref="EvalAsynchronousHostOperationCountedAsync"/>.
    /// </summary>
    private static async ValueTask<EvalResult<ZeroArgPropertyResult>> GetOrEvaluateZeroArgPropertyResultCoreAsync(
        Algorithm? owner,
        Property binding,
        ZeroArgPropertyAccessKind accessKind,
        Algorithm resolvedAlgorithm,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (owner is null)
            return await EvaluateZeroArgPropertyResultAsync(resolvedAlgorithm, ctx, valEnv).ConfigureAwait(false);

        // The async twin family is entered only when the run's cache is async-capable,
        // and the cache reference is never replaced during a run, so a non-async cache
        // here is an evaluator ownership bug — fail loud rather than silently blocking
        // or bypassing the host's cache.
        if (ctx.ZeroArgPropertyResultCache is not IAsyncZeroArgPropertyResultCache asyncCache)
        {
            throw new InvalidOperationException(
                "Async evaluation requires an async-capable zero-argument property result cache on the run context.");
        }

        return await asyncCache.GetOrEvaluateAsync(
            new ZeroArgPropertyExecution(
                owner,
                binding,
                accessKind,
                ValueEnvironmentCacheIdentity(valEnv),
                ctx.AlgEnv,
                ctx.CountedParamEnv,
                // The budget is the run identity, exactly as on the synchronous seam.
                ctx.Budget),
            () => EvaluateZeroArgPropertyResultAsync(resolvedAlgorithm, ctx, valEnv)).ConfigureAwait(false);
    }

    /// <summary>MIRROR OF <see cref="EvalZeroArgPropertyAccessCounted(Algorithm?, Property, ZeroArgPropertyAccessKind, Algorithm, EvalCtx, IReadOnlyList{ValueTuple{string, Result}})"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalZeroArgPropertyAccessCountedAsync(
        Algorithm? owner,
        Property binding,
        ZeroArgPropertyAccessKind accessKind,
        Algorithm resolvedAlgorithm,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var propertyR = await GetOrEvaluateZeroArgPropertyResultAsync(
            owner, binding, accessKind, resolvedAlgorithm, ctx, valEnv).ConfigureAwait(false);
        return propertyR.IsError
            ? propertyR.Error
            : EvalResult<CountedResult>.Ok(new CountedResult(propertyR.Value.Value, propertyR.Value.EmittedCount));
    }

    /// <summary>MIRROR OF the <see cref="ResolvedLexicalProperty"/> overload of <c>EvalZeroArgPropertyAccessCounted</c> — keep in lock-step.</summary>
    private static ValueTask<EvalResult<CountedResult>> EvalZeroArgPropertyAccessCountedAsync(
        ResolvedLexicalProperty resolvedProperty,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
        => EvalZeroArgPropertyAccessCountedAsync(
            resolvedProperty.Owner,
            resolvedProperty.Binding,
            ZeroArgPropertyAccessKind.CountedLexical,
            resolvedProperty.ResolvedAlgorithm,
            ctx,
            valEnv);

    /// <summary>
    /// Awaits one ASYNCHRONOUS host operation at its wrapper-body evaluation site — the
    /// public Phase 3 counterpart of the internal cache seam await. Argument collection
    /// and the result contract are the synchronous
    /// <see cref="InvokeSynchronousHostOperation"/>'s, with exactly one difference: the
    /// implementation's <see cref="ValueTask{TResult}"/> is awaited, so an incomplete
    /// awaitable suspends the whole spine and resumes it — never re-invoking the
    /// operation — when the host completes it. Host exceptions and faulted awaitables
    /// propagate unchanged; the invocation runs inside the wrapper call's
    /// already-charged region, so no budget counter moves here.
    /// </summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalAsynchronousHostOperationCountedAsync(
        HostOperation hostOperation,
        IReadOnlyList<string> argNames,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (ValidateHostOperationNativeSignature(hostOperation, argNames) is { } signatureError)
            return signatureError;

        var argumentsR = CollectHostOperationArguments(argNames, ctx, valEnv);
        if (argumentsR.IsError) return argumentsR.Error;

        var value = await hostOperation.AsynchronousImplementation!(
            argumentsR.Value, ctx.Budget.CancellationToken).ConfigureAwait(false);

        // Deterministic post-resumption observation: a token cancelled while the run
        // was suspended in the host operation is honored as soon as evaluation resumes,
        // rather than at whichever charging chokepoint happens to come next.
        // Observation-only — no counter moves, matching every other observation point.
        ctx.Budget.ObserveCancellation();

        // Shared canonical-value boundary (null contract included) — see
        // NormalizeHostOperationValue; a cancelled-while-suspended run was already
        // honored above, so only genuinely successful values are normalized.
        var normalized = NormalizeHostOperationValue(hostOperation, value);
        return EvalResult<CountedResult>.Ok(new CountedResult(normalized, normalized.ValueCount()));
    }

    /// <summary>MIRROR OF <see cref="EvalResolvedAlgOutputForValueDemand"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<Result>> EvalResolvedAlgOutputForValueDemandAsync(
        Algorithm algorithm,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (ctx.Budget.TryEnterArgumentEvaluation() is { } limitError)
            return limitError;
        try
        {
            return await EvalAlgOutputValueAsync(algorithm, ctx, valEnv).ConfigureAwait(false);
        }
        finally
        {
            ctx.Budget.ExitInvocation();
        }
    }

    // ── Call twins ──────────────────────────────────────────────────────────

    /// <summary>
    /// MIRROR OF <see cref="EvalCallCountedExpr"/> — keep in lock-step. The sequence
    /// pipeline attempt is omitted: the async root context pins fusion off, so the
    /// synchronous counterpart would not fuse either; the guard makes the pinning
    /// violation loud instead of silently diverging.
    /// </summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalCallCountedExprAsync(
        Expr func,
        OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        ThrowIfAsyncStrategyPinningViolated(ctx);

        var diagnosticName = CallDiagnosticName.FromExpression(func);
        var calleeR = ResolveAlg(func, ctx);
        if (calleeR.IsError)
            return new EvalError.WithContext(CtxCall(diagnosticName, ctx), calleeR.Error) { Span = calleeR.Error.Span };

        return WithCallCtx(
            diagnosticName,
            ctx,
            await EvalResolvedCallCountedAsync(calleeR.Value, args, ctx, valEnv, diagnosticName).ConfigureAwait(false));
    }

    /// <summary>
    /// The async twin family mirrors the GENERIC loop and sequence strategies only, and
    /// the async root context construction pins both optimizations off. Reaching a twin
    /// with either flag enabled is an evaluator ownership bug — fail loud (like
    /// <see cref="EvaluationBudget.ExitInvocation"/> underflow) rather than silently
    /// running a strategy the twin family does not mirror.
    /// </summary>
    private static void ThrowIfAsyncStrategyPinningViolated(EvalCtx ctx)
    {
        if (ctx.EnableLoopOptimization || ctx.EnableSequencePipelineOptimization)
        {
            throw new InvalidOperationException(
                "Async evaluation requires the generic loop and sequence strategies; the async root context must pin both optimizations off.");
        }
    }

    /// <summary>MIRROR OF <see cref="EvalResolvedCallCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalResolvedCallCountedAsync(
        Algorithm callee,
        OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        CallDiagnosticName calleeName,
        CallArgumentAssembly argumentAssembly = CallArgumentAssembly.OrdinaryArguments)
    {
        if (callee is Algorithm.Builtin(var builtinId))
        {
            var argAlgsR = ResolveArgAlgsWithSequenceSpread(args, ctx, valEnv);
            if (argAlgsR.IsError) return argAlgsR.Error;
            return await ApplyBuiltinCountedResolvedAsync(builtinId, argAlgsR.Value, ctx, valEnv).ConfigureAwait(false);
        }

        if (TryGetFlatBinderUserEquivalent(callee) is { } simpleCallee)
            return await EvalUserCallCountedAsync(
                simpleCallee,
                args,
                ctx,
                valEnv,
                argumentAssembly,
                calleeName).ConfigureAwait(false);

        if (callee is Algorithm.Conditional)
            return await EvalConditionalCallCountedAsync(callee, args, ctx, valEnv, calleeName, argumentAssembly).ConfigureAwait(false);

        return await EvalUserCallCountedAsync(
            callee,
            args,
            ctx,
            valEnv,
            argumentAssembly,
            calleeName).ConfigureAwait(false);
    }

    /// <summary>MIRROR OF <see cref="EvalUserCallCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalUserCallCountedAsync(
        Algorithm callee, OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        CallArgumentAssembly argumentAssembly,
        CallDiagnosticName calleeName)
    {
        // Charged dynamic invocation boundary (see EvaluationBudget).
        if (ctx.Budget.TryEnterInvocation() is { } limitError)
            return AtSpanIfMissing(limitError, FirstSpan(args));

        try
        {
            return await EvalUserCallCountedCoreAsync(callee, args, ctx, valEnv, argumentAssembly, calleeName).ConfigureAwait(false);
        }
        finally
        {
            ctx.Budget.ExitInvocation();
        }
    }

    /// <summary>MIRROR OF <see cref="EvalUserCallCountedCore"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalUserCallCountedCoreAsync(
        Algorithm callee, OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        CallArgumentAssembly argumentAssembly,
        CallDiagnosticName calleeName)
    {
        if (callee.Output.Count == 0)
            return new EvalError.MissingOutput();

        if (callee is Algorithm.User { IsAssignmentDeconstructionHelper: true } deconstructionHelper
            && await TryProjectSharedDeconstructionTargetAsync(
                deconstructionHelper, args, ctx, valEnv, calleeName, argumentAssembly).ConfigureAwait(false) is { } sharedTarget)
        {
            return sharedTarget.IsError
                ? sharedTarget.Error
                : EvalResult<CountedResult>.Ok(new CountedResult(sharedTarget.Value, sharedTarget.Value.ValueCount()));
        }

        var signature = CallableSignature.FromAlgorithm(calleeName.StructuralName, callee);
        var bindingPlan = CallableBindingPlan.FromSignature(signature);

        if (bindingPlan.RequiresPatternedBinding)
        {
            var bindingsR = await BindPatternedUserCallAsync(callee, args, ctx, valEnv, calleeName, argumentAssembly).ConfigureAwait(false);
            if (bindingsR.IsError) return bindingsR.Error;

            var bindings = bindingsR.Value;
            var groupedCtx = WithUserCallBindingEnvironments(ctx, bindings, callee.Params);
            var groupedEnv = Concat(bindings.ValueBindings, valEnv);
            return ReCountValueBoundary(await EvalAlgOutputCountedCoreAsync(callee, groupedCtx, groupedEnv).ConfigureAwait(false));
        }

        if (IsDeconstructionUserCallShape(signature))
        {
            var bindingsR = await BindDeconstructionUserCallAsync(callee, args, ctx, valEnv, calleeName, argumentAssembly).ConfigureAwait(false);
            if (bindingsR.IsError) return bindingsR.Error;

            var bindings = bindingsR.Value;
            var deconstructionCtx = WithUserCallBindingEnvironments(ctx, bindings, callee.Params);
            var deconstructionEnv = Concat(bindings.ValueBindings, valEnv);
            return ReCountValueBoundary(await EvalAlgOutputCountedCoreAsync(callee, deconstructionCtx, deconstructionEnv).ConfigureAwait(false));
        }

        if (!TryGetPlanDerivedFlatFixedParameterNames(bindingPlan, out var flatFixedParams))
            flatFixedParams = callee.Params;

        var flatBindingsR = await BindFlatFixedUserCallArgumentsAsync(
            callee,
            calleeName,
            flatFixedParams,
            args,
            ctx,
            valEnv).ConfigureAwait(false);
        if (flatBindingsR.IsError) return flatBindingsR.Error;

        var flatBindings = flatBindingsR.Value;
        return ReCountValueBoundary(await EvalAlgOutputCountedCoreAsync(callee, flatBindings.Context, flatBindings.ValueEnvironment).ConfigureAwait(false));
    }

    /// <summary>MIRROR OF <see cref="TryProjectSharedDeconstructionTarget"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<Result>?> TryProjectSharedDeconstructionTargetAsync(
        Algorithm.User helper,
        OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        CallDiagnosticName calleeName,
        CallArgumentAssembly argumentAssembly)
    {
        var group = helper.AssignmentDeconstructionGroup;
        if (group is null)
            return null;

        var execution = new DeconstructionBindingExecution(
            group,
            DeconstructionOwnerIdentity(ctx),
            ValueEnvironmentCacheIdentity(valEnv),
            ctx.AlgEnv,
            ctx.CountedParamEnv);

        var sharedR = await ctx.DeconstructionBindingCache.GetOrBindAsync(
            execution,
            async () =>
            {
                var bindingsR = await BindPatternedUserCallAsync(helper, args, ctx, valEnv, calleeName, argumentAssembly).ConfigureAwait(false);
                if (bindingsR.IsError)
                    return bindingsR.Error;

                // Materialize the shared bind as the bound values in TARGET order —
                // identical projection to the synchronous twin.
                var bindings = bindingsR.Value;
                var valueByName = new Dictionary<string, Result>(bindings.ValueBindings.Count, StringComparer.Ordinal);
                foreach (var (name, value) in bindings.ValueBindings)
                    valueByName[name] = value;
                foreach (var (name, counted) in bindings.CountedBindings)
                    valueByName[name] = counted.Value;

                var parameters = helper.Parameters;
                var projected = new Result[parameters.Count];
                for (var i = 0; i < parameters.Count; i++)
                {
                    if (!valueByName.TryGetValue(parameters[i].Name, out var value))
                        return new EvalError.UnknownName(parameters[i].Name);
                    projected[i] = value;
                }
                return EvalResult<IReadOnlyList<Result>>.Ok(projected);
            }).ConfigureAwait(false);

        if (sharedR.IsError)
            return sharedR.Error;

        var values = sharedR.Value;
        var index = helper.AssignmentDeconstructionTargetIndex;
        if ((uint)index >= (uint)values.Count)
            return null;

        return EvalResult<Result>.Ok(values[index]);
    }

    /// <summary>MIRROR OF <see cref="EvalConditionalCallCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalConditionalCallCountedAsync(
        Algorithm callee, OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        CallDiagnosticName calleeName,
        CallArgumentAssembly argumentAssembly = CallArgumentAssembly.OrdinaryArguments)
    {
        // Charged dynamic invocation boundary; this counted core owns the
        // boundary for both counted evaluation and its plain projection.
        if (ctx.Budget.TryEnterInvocation() is { } limitError)
            return AtSpanIfMissing(limitError, FirstSpan(args));

        try
        {
            return await EvalConditionalCallCountedCoreAsync(callee, args, ctx, valEnv, calleeName, argumentAssembly).ConfigureAwait(false);
        }
        finally
        {
            ctx.Budget.ExitInvocation();
        }
    }

    /// <summary>MIRROR OF <see cref="EvalConditionalCallCountedCore"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalConditionalCallCountedCoreAsync(
        Algorithm callee, OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        CallDiagnosticName calleeName,
        CallArgumentAssembly argumentAssembly)
    {
        var argResultsR = await EvalConditionalCallArgumentsAsync(args, ctx, valEnv, argumentAssembly).ConfigureAwait(false);
        if (argResultsR.IsError) return argResultsR.Error;
        var argResults = argResultsR.Value;

        if (callee.HasDuplicateBranchPatterns())
            return new EvalError.DuplicateBranchPattern();

        var match = MatchCallBranches(callee.Branches, argResults);
        if (match is null)
            return new EvalError.NoMatchingBranch(calleeName.Render(ctx));

        var (branch, bindings) = match.Value;
        var wiredBody = ChildOf(callee, branch.Body);
        var shadowedNames = bindings.Select(static binding => binding.Item1).ToArray();
        var newCtx = ctx.Push(callee)
            .WithCountedParamEnv(ShadowCountedParamEnv(ctx.CountedParamEnv, shadowedNames));
        var newEnv = Concat(bindings, valEnv);
        return ReCountValueBoundary(await EvalAlgOutputCountedCoreAsync(wiredBody, newCtx, newEnv).ConfigureAwait(false));
    }

    /// <summary>MIRROR OF <see cref="EvalConditionalCallArguments"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<IReadOnlyList<Result>>> EvalConditionalCallArgumentsAsync(
        OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        CallArgumentAssembly argumentAssembly)
    {
        var inputsR = await BuildCallArgumentInputsAsync(args, ctx, valEnv, argumentAssembly).ConfigureAwait(false);
        if (inputsR.IsError) return inputsR.Error;

        var argResults = new List<Result>(inputsR.Value.Count);
        foreach (var input in inputsR.Value)
        {
            if (input.Value is null)
                return input.ValueError ?? new EvalError.BadArity();

            argResults.Add(input.Value);
        }

        return EvalResult<IReadOnlyList<Result>>.Ok(argResults);
    }

    // ── Argument-assembly and binding twins ─────────────────────────────────

    /// <summary>MIRROR OF <see cref="BuildCallArgumentInputs"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<IReadOnlyList<ParameterPatternInput>>> BuildCallArgumentInputsAsync(
        OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        CallArgumentAssembly argumentAssembly = CallArgumentAssembly.OrdinaryArguments,
        bool includeExplicitSequenceValueItems = false)
    {
        var maybeAlgsR = TryResolveArgAlgs(args, ctx);
        if (maybeAlgsR.IsError) return maybeAlgsR.Error;

        var maybeAlgs = maybeAlgsR.Value;
        var inputs = new List<ParameterPatternInput>();

        for (var index = 0; index < args.Count; index++)
        {
            var argExpr = args[index];
            var maybeAlg = index < maybeAlgs.Count ? maybeAlgs[index] : null;
            var isDotReceiverSegment = IsInjectedDotReceiverSegment(argumentAssembly, index);

            if (argExpr is Expr.SequenceSpread && !isDotReceiverSegment)
            {
                var suppliedR = await EvalCountedAsync(argExpr, ctx, valEnv).ConfigureAwait(false);
                if (suppliedR.IsError)
                    return suppliedR.Error;

                foreach (var value in CountedTopLevelValues(suppliedR.Value))
                    inputs.Add(new ParameterPatternInput(value, Algorithm: null, ValueError: null, ExplicitSequenceValueItems: null));

                continue;
            }

            var preparedR = await PrepareCallArgumentEvaluationAsync(
                argExpr,
                ctx,
                valEnv,
                isDotReceiverSegment,
                includeExplicitSequenceValueItems).ConfigureAwait(false);
            if (preparedR.IsOk)
            {
                inputs.Add(new ParameterPatternInput(
                    preparedR.Value.Counted.Value,
                    maybeAlg,
                    ValueError: null,
                    preparedR.Value.ExplicitSequenceValueItems,
                    CollectingSegmentEmittedCount: isDotReceiverSegment
                        ? preparedR.Value.Counted.EmittedCount
                        : null));
                continue;
            }

            if (maybeAlg is not null)
            {
                inputs.Add(new ParameterPatternInput(Value: null, maybeAlg, preparedR.Error, ExplicitSequenceValueItems: null));
                continue;
            }

            return preparedR.Error;
        }

        return EvalResult<IReadOnlyList<ParameterPatternInput>>.Ok(inputs);
    }

    /// <summary>MIRROR OF <see cref="PrepareCallArgumentEvaluation"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<PreparedCallArgumentEvaluation>> PrepareCallArgumentEvaluationAsync(
        Expr argExpr,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        bool isDotReceiverSegment,
        bool includeExplicitSequenceValueItems)
    {
        if (includeExplicitSequenceValueItems && argExpr is Expr.Capture(var captureBody))
        {
            var captureSpan = PreferExpressionSpan(argExpr.Span, captureBody);
            var capturePreparedR = WithSpan(captureSpan, await EvalCapturePreparedCoreAsync(captureBody, ctx, valEnv).ConfigureAwait(false));
            if (capturePreparedR.IsError) return capturePreparedR.Error;

            var captureCounted = PrepareCallArgumentBoundaryCount(
                capturePreparedR.Value.Counted,
                isDotReceiverSegment);
            return EvalResult<PreparedCallArgumentEvaluation>.Ok(new(
                captureCounted,
                capturePreparedR.Value.OutputSlots));
        }

        if (includeExplicitSequenceValueItems && argExpr is Expr.AlgorithmExpr(var algorithm))
        {
            var wired = WireToCaller(ctx, algorithm);
            if (wired.Params.Count == 0)
            {
                var blockSpan = PreferExpressionSpan(argExpr.Span, wired.Output);
                var preparedR = WithSpan(blockSpan, await EvalAlgOutputPreparedCoreAsync(wired, ctx, valEnv).ConfigureAwait(false));
                if (preparedR.IsError) return preparedR.Error;

                var counted = PrepareCallArgumentBoundaryCount(
                    preparedR.Value.Counted,
                    isDotReceiverSegment);
                return EvalResult<PreparedCallArgumentEvaluation>.Ok(new(
                    counted,
                    preparedR.Value.OutputSlots));
            }
        }

        var evaluatedR = isDotReceiverSegment
            ? await EvalDotReceiverCallSegmentCountedAsync(argExpr, ctx, valEnv).ConfigureAwait(false)
            : await EvalCountedAsync(argExpr, ctx, valEnv).ConfigureAwait(false);
        return evaluatedR.IsError
            ? evaluatedR.Error
            : EvalResult<PreparedCallArgumentEvaluation>.Ok(new(evaluatedR.Value, null));
    }

    /// <summary>MIRROR OF <see cref="EvalDotReceiverCallSegmentCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalDotReceiverCallSegmentCountedAsync(
        Expr receiver,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (receiver is Expr.Capture(var captureBody))
            return WithSpan(PreferExpressionSpan(receiver.Span, captureBody), await EvalCaptureCountedCoreAsync(captureBody, ctx, valEnv).ConfigureAwait(false));

        if (receiver is Expr.AlgorithmExpr(var algorithm))
        {
            var wired = WireToCaller(ctx, algorithm);
            if (wired.Params.Count == 0)
                return WithSpan(PreferExpressionSpan(receiver.Span, wired.Output), await EvalAlgOutputCountedCoreAsync(wired, ctx, valEnv).ConfigureAwait(false));
        }

        return await EvalCountedAsync(receiver, ctx, valEnv).ConfigureAwait(false);
    }

    /// <summary>MIRROR OF <see cref="BindPatternedUserCall"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<UserCallBindings>> BindPatternedUserCallAsync(
        Algorithm callee,
        OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        CallDiagnosticName calleeName,
        CallArgumentAssembly argumentAssembly = CallArgumentAssembly.OrdinaryArguments)
    {
        if (callee is Algorithm.User { IsAssignmentDeconstructionHelper: true })
            ctx.Observations?.RecordDeconstructionFullBind();

        var inputsR = await BuildCallArgumentInputsAsync(
            args,
            ctx,
            valEnv,
            argumentAssembly,
            includeExplicitSequenceValueItems: true).ConfigureAwait(false);
        if (inputsR.IsError) return inputsR.Error;

        var bindingsR = BindParameterPatternList(
            callee.ParameterPatterns,
            inputsR.Value,
            ctx,
            allowAlgorithmBindings: true,
            (required, actual) => new EvalError.ArityMismatch(required, actual)
            {
                Signature = CallableSignature.FromAlgorithm(calleeName.Render(ctx), callee),
                InferredImplicitParameters = ImplicitParameterProvenance.CollectFrom(callee.Parameters),
            });

        // Assignment-deconstruction shape failures are rephrased against the WRITTEN
        // pattern — identical rule and conditions to the synchronous twin.
        if (bindingsR.IsError
            && callee is Algorithm.User { IsAssignmentDeconstructionHelper: true }
            && TryGetDeconstructionShapeMismatch(bindingsR.Error) is { } deconstructionMismatch
            && inputsR.Value.All(static input => input.Value is not null))
        {
            return new EvalError.WithContext(
                new DeconstructionBindingContext(
                    callee.Parameters.Select(static parameter => parameter.DisplayName).ToList(),
                    callee.Parameters.Any(static parameter => parameter.Kind == ParameterKind.Collecting)),
                deconstructionMismatch);
        }

        return bindingsR;
    }

    /// <summary>MIRROR OF <see cref="BindDeconstructionUserCall"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<UserCallBindings>> BindDeconstructionUserCallAsync(
        Algorithm callee,
        OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        CallDiagnosticName calleeName,
        CallArgumentAssembly argumentAssembly = CallArgumentAssembly.OrdinaryArguments)
    {
        var inputsR = await BuildCallArgumentInputsAsync(args, ctx, valEnv, argumentAssembly).ConfigureAwait(false);
        if (inputsR.IsError) return inputsR.Error;

        return BindParameterPatternList(
            callee.ParameterPatterns,
            inputsR.Value,
            ctx,
            allowAlgorithmBindings: true,
            (required, actual) =>
            {
                var renderedName = calleeName.Render(ctx);
                return VariadicBindingArityMismatch(
                    renderedName,
                    required,
                    actual,
                    CallableSignature.FromAlgorithm(renderedName, callee));
            });
    }

    /// <summary>MIRROR OF <see cref="BindFlatFixedUserCallArguments"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<FlatFixedUserCallBindings>> BindFlatFixedUserCallArgumentsAsync(
        Algorithm callee,
        CallDiagnosticName calleeName,
        IReadOnlyList<string> parameterNames,
        OutputBundle args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var paramCount = parameterNames.Count;

        var inputsR = await BuildCallArgumentInputsAsync(args, ctx, valEnv).ConfigureAwait(false);
        if (inputsR.IsError) return inputsR.Error;

        var slots = inputsR.Value
            .Select(static input => new FlatFixedCallSlot(input.Value, input.Algorithm, input.ValueError))
            .ToList();

        if (slots.Count > paramCount)
            return new EvalError.ArityMismatch(paramCount, slots.Count)
            {
                Signature = CallableSignature.FromAlgorithm(calleeName.Render(ctx), callee),
                InferredImplicitParameters = ImplicitParameterProvenance.CollectFrom(callee.Parameters),
            };

        var algBindings = new List<(string Name, Algorithm Value, EvalError? ValueError)>();
        var valueParams = new List<string>();
        var valueResults = new List<Result>();

        for (var i = 0; i < paramCount; i++)
        {
            if (i >= slots.Count)
            {
                valueParams.Add(parameterNames[i]);
                continue;
            }

            var slot = slots[i];
            if (slot.Algorithm is not null)
            {
                algBindings.Add((
                    parameterNames[i],
                    slot.Algorithm,
                    RetainResourceLimitForAlgorithmBinding(slot.ValueError)));
            }

            if (slot.Value is not null)
            {
                valueParams.Add(parameterNames[i]);
                valueResults.Add(slot.Value);
            }
        }

        var argEnvR = BindParams(valueParams, valueResults);
        if (argEnvR.IsError)
        {
            if (argEnvR.Error is EvalError.ArityMismatch arityMismatch)
                return arityMismatch with
                {
                    Signature = CallableSignature.FromAlgorithm(calleeName.Render(ctx), callee),
                    InferredImplicitParameters = ImplicitParameterProvenance.CollectFrom(callee.Parameters),
                };

            return argEnvR.Error;
        }

        var boundCtx = ctx
            .WithAlgEnv(Concat(algBindings, ctx.AlgEnv))
            .WithCountedParamEnv(ShadowCountedParamEnv(ctx.CountedParamEnv, parameterNames));
        var boundEnv = Concat(argEnvR.Value, valEnv);
        return EvalResult<FlatFixedUserCallBindings>.Ok(new FlatFixedUserCallBindings(boundCtx, boundEnv));
    }

    // ── Builtin twins ───────────────────────────────────────────────────────

    /// <summary>MIRROR OF <see cref="ApplyBuiltinCountedResolved"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> ApplyBuiltinCountedResolvedAsync(
        BuiltinId builtin,
        IReadOnlyList<ResolvedArgumentAlgorithm> resolvedArgs,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (GetSequenceBuiltinMetadata(builtin) is { } metadata)
            return await ApplyBuiltinCountedSequenceAsync(builtin, metadata, resolvedArgs, ctx, valEnv).ConfigureAwait(false);

        var expandedArgsR = await ExpandSequenceSpreadBuiltinArgumentsAsync(resolvedArgs, ctx, valEnv).ConfigureAwait(false);
        if (expandedArgsR.IsError) return expandedArgsR.Error;
        var args = expandedArgsR.Value;

        switch (builtin, args.Count)
        {
            case (BuiltinId.@if, 3):
                {
                    var condR = await EvalResolvedArgumentValueAsync(args[0], ctx, valEnv).ConfigureAwait(false);
                    if (condR.IsError) return condR.Error;
                    var truth = condR.Value.TruthValue();
                    if (truth is null) return new EvalError.BadArity();

                    // The selected branch is one value boundary — see the synchronous twin.
                    var branchR = truth.Value
                        ? await EvalResolvedArgumentCountedAsync(args[1], ctx, valEnv).ConfigureAwait(false)
                        : await EvalResolvedArgumentCountedAsync(args[2], ctx, valEnv).ConfigureAwait(false);
                    if (branchR.IsError) return branchR.Error;
                    return EvalResult<CountedResult>.Ok(
                        new CountedResult(branchR.Value.Value, branchR.Value.Value.ValueCount()));
                }

            case (BuiltinId.@while, _) when args.Count >= 2:
                {
                    var stepR = ResolveArgumentAlgorithm(args[0], ctx);
                    if (stepR.IsError) return stepR.Error;
                    var initialStateR = await EvalInitialLoopStateSlotsAsync(args.Skip(1).ToList(), ctx, valEnv).ConfigureAwait(false);
                    if (initialStateR.IsError) return initialStateR.Error;
                    return await WhileLoopCountedAsync(stepR.Value, initialStateR.Value, ctx, valEnv).ConfigureAwait(false);
                }

            case (BuiltinId.@repeat, _) when args.Count >= 3:
                {
                    var stepR = ResolveArgumentAlgorithm(args[0], ctx);
                    if (stepR.IsError) return stepR.Error;
                    var countR = await EvalResolvedArgumentValueAsync(args[1], ctx, valEnv).ConfigureAwait(false);
                    if (countR.IsError) return countR.Error;
                    var nR = ExpectWholeInt(countR.Value, "Repeat count");
                    if (nR.IsError) return nR.Error;
                    // Domain check BEFORE narrowing, mirroring the synchronous twin.
                    if (nR.Value < 0) return new EvalError.IllegalInEval("Repeat count must be >= 0");
                    var n = nR.Value >= long.MaxValue ? long.MaxValue : (long)nR.Value;

                    var initialStateR = await EvalInitialLoopStateSlotsAsync(args.Skip(2).ToList(), ctx, valEnv).ConfigureAwait(false);
                    if (initialStateR.IsError) return initialStateR.Error;
                    return await RepeatLoopCountedAsync(stepR.Value, n, initialStateR.Value, ctx, valEnv).ConfigureAwait(false);
                }

            case (BuiltinId.@atoms, 1):
                {
                    var atomsR = await EvalResolvedArgumentValueAsync(args[0], ctx, valEnv).ConfigureAwait(false);
                    if (atomsR.IsError) return atomsR.Error;
                    return MakeLanguageAtomsResult(ctx, atomsR.Value);
                }

            case (BuiltinId.@range, 2):
                {
                    var rangeR = await EvalBuiltinRangeArgumentsAsync(args, ctx, valEnv).ConfigureAwait(false);
                    if (rangeR.IsError) return rangeR.Error;

                    // A list value is always one visible value, including `[]`.
                    var rangeValueR = BuildInclusiveRangeChecked(ctx, rangeR.Value);
                    return rangeValueR.IsError
                        ? rangeValueR.Error
                        : EvalResult<CountedResult>.Ok(new CountedResult(rangeValueR.Value, 1));
                }

            default:
                return WrongBuiltinArity(builtin, args.Count);
        }
    }

    /// <summary>
    /// MIRROR OF <see cref="EvalBuiltinRangeArguments"/> — keep in lock-step.
    /// Only child-evaluation sequencing is twinned; bound VALIDATION is the shared
    /// <see cref="ValidateRangeBound"/>, so the range safety policy (whole integer,
    /// magnitude within the exact-unit-step domain) cannot drift between the sync
    /// and async paths.
    /// </summary>
    private static async ValueTask<EvalResult<InclusiveRange>> EvalBuiltinRangeArgumentsAsync(
        IReadOnlyList<ResolvedArgumentAlgorithm> args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (args.Count != 2)
            return WrongBuiltinArity(BuiltinId.@range, args.Count);

        var startR = await EvalResolvedArgumentValueAsync(args[0], ctx, valEnv).ConfigureAwait(false);
        if (startR.IsError) return startR.Error;
        var startIntR = ValidateRangeBound(startR.Value, "range start");
        if (startIntR.IsError) return startIntR.Error;

        var stopR = await EvalResolvedArgumentValueAsync(args[1], ctx, valEnv).ConfigureAwait(false);
        if (stopR.IsError) return stopR.Error;
        var stopIntR = ValidateRangeBound(stopR.Value, "range stop");
        if (stopIntR.IsError) return stopIntR.Error;

        return EvalResult<InclusiveRange>.Ok(new InclusiveRange(startIntR.Value, stopIntR.Value));
    }

    /// <summary>MIRROR OF <see cref="EvalInitialLoopStateSlots"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<IReadOnlyList<Result>>> EvalInitialLoopStateSlotsAsync(
        IReadOnlyList<ResolvedArgumentAlgorithm> initArgs,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var stateSlots = new List<Result>(initArgs.Count);
        foreach (var init in initArgs)
        {
            var slotR = await EvalResolvedArgumentValueAsync(init, ctx, valEnv).ConfigureAwait(false);
            if (slotR.IsError) return slotR.Error;
            stateSlots.Add(slotR.Value);
        }

        return EvalResult<IReadOnlyList<Result>>.Ok(stateSlots);
    }

    /// <summary>MIRROR OF <see cref="EvalResolvedArgumentCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalResolvedArgumentCountedAsync(
        ResolvedArgumentAlgorithm arg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
        => arg.PreparedValue is { } prepared
            ? EvalResult<CountedResult>.Ok(prepared)
            : arg.Algorithm is { } algorithm
                ? await EvalArgumentAlgOutputCountedAsync(algorithm, ctx, valEnv).ConfigureAwait(false)
                : new EvalError.BadArity();

    /// <summary>MIRROR OF <see cref="EvalResolvedArgument"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<Result>> EvalResolvedArgumentValueAsync(
        ResolvedArgumentAlgorithm arg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var countedR = await EvalResolvedArgumentCountedAsync(arg, ctx, valEnv).ConfigureAwait(false);
        return countedR.IsError
            ? countedR.Error
            : EvalResult<Result>.Ok(countedR.Value.Value);
    }

    /// <summary>MIRROR OF <see cref="EvalArgumentAlgOutputCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalArgumentAlgOutputCountedAsync(
        Algorithm algorithm,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (ctx.Budget.TryEnterArgumentEvaluation() is { } limitError)
            return limitError;
        try
        {
            return await EvalAlgOutputCountedCoreAsync(algorithm, ctx, valEnv).ConfigureAwait(false);
        }
        finally
        {
            ctx.Budget.ExitInvocation();
        }
    }

    /// <summary>MIRROR OF <see cref="ExpandSequenceSpreadBuiltinArguments"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<IReadOnlyList<ResolvedArgumentAlgorithm>>> ExpandSequenceSpreadBuiltinArgumentsAsync(
        IReadOnlyList<ResolvedArgumentAlgorithm> args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var expanded = new List<ResolvedArgumentAlgorithm>(args.Count);
        foreach (var arg in args)
        {
            if (!arg.SpreadsSequence)
            {
                expanded.Add(arg);
                continue;
            }

            var outputR = await EvalResolvedArgumentCountedAsync(arg, ctx, valEnv).ConfigureAwait(false);
            if (outputR.IsError) return outputR.Error;

            foreach (var value in CountedTopLevelValues(outputR.Value))
            {
                var prepared = new CountedResult(value, 1);
                expanded.Add(new ResolvedArgumentAlgorithm(
                    Algorithm: null,
                    SpreadsSequence: false)
                {
                    PreparedValue = prepared,
                });
            }
        }

        return EvalResult<IReadOnlyList<ResolvedArgumentAlgorithm>>.Ok(expanded);
    }

    /// <summary>MIRROR OF <see cref="BuildCallableCallItems"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<IReadOnlyList<VariadicCallItem>>> BuildCallableCallItemsAsync(
        IReadOnlyList<ResolvedArgumentAlgorithm> args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var items = new List<VariadicCallItem>();
        foreach (var resolvedArg in args)
        {
            var arg = resolvedArg.Algorithm;

            // Callback/function arguments stay unevaluated — see the synchronous twin.
            if (arg is not null && (arg.Params.Count > 0 || arg.ParameterPatterns.Count > 0))
            {
                items.Add(new VariadicCallItem(
                    Value: null,
                    arg,
                    ValueError: null,
                    resolvedArg.PreparedValue));
                continue;
            }

            var outputR = resolvedArg.PreparedValue is { } prepared
                ? EvalResult<CountedResult>.Ok(prepared)
                : arg is { } algorithm
                    ? await EvalArgumentAlgOutputCountedAsync(algorithm, ctx, valEnv).ConfigureAwait(false)
                    : EvalResult<CountedResult>.Err(new EvalError.BadArity());
            if (outputR.IsOk)
            {
                if (resolvedArg.SpreadsSequence)
                {
                    foreach (var value in CountedTopLevelValues(outputR.Value))
                    {
                        items.Add(new VariadicCallItem(
                            value,
                            arg,
                            ValueError: null,
                            new CountedResult(value, 1)));
                    }
                }
                else
                {
                    items.Add(new VariadicCallItem(
                        outputR.Value.Value,
                        arg,
                        ValueError: null,
                        outputR.Value));
                }

                continue;
            }

            items.Add(new VariadicCallItem(Value: null, arg, outputR.Error));
        }

        return EvalResult<IReadOnlyList<VariadicCallItem>>.Ok(items);
    }

    /// <summary>MIRROR OF <see cref="BindSequenceBuiltinArguments"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<BoundSequenceBuiltinArguments>> BindSequenceBuiltinArgumentsAsync(
        BuiltinId builtin,
        SequenceBuiltinMetadata metadata,
        IReadOnlyList<ResolvedArgumentAlgorithm> args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var descriptor = BuiltinRegistry.GetBuiltin(builtin);
        var signature = descriptor.PlainSignature;
        var itemsR = await BuildCallableCallItemsAsync(args, ctx, valEnv).ConfigureAwait(false);
        if (itemsR.IsError) return itemsR.Error;

        // Collection builtins are ordinary fixed-arity callables — see the synchronous twin.
        var items = itemsR.Value;
        var expectedArgCount = 1 + metadata.SuffixArgs.Count;
        if (items.Count != expectedArgCount)
        {
            return new EvalError.ArityMismatch(expectedArgCount, items.Count)
            {
                Signature = signature,
            };
        }

        var collectionItem = items[0];
        if (collectionItem.Value is null)
            return collectionItem.ValueError ?? new EvalError.BadArity();

        var collectionValues = BuiltinCollectionItems(collectionItem.Value);

        var collected = new CollectedSequenceBuiltinInput([collectionValues], collectionValues);
        var preparedInputR = PrepareSequenceBuiltinInput(builtin, metadata, collected);
        if (preparedInputR.IsError) return preparedInputR.Error;

        var suffixArgs = new List<PreparedSequenceBuiltinSuffixArg>(metadata.SuffixArgs.Count);
        for (var index = 0; index < metadata.SuffixArgs.Count; index++)
        {
            var preparedArgR = PrepareSequenceBuiltinSuffixArg(
                builtin,
                metadata.SuffixArgs[index],
                items[1 + index],
                ctx);
            if (preparedArgR.IsError) return preparedArgR.Error;

            suffixArgs.Add(preparedArgR.Value);
        }

        var iterationItems = collectionValues
            .Select(static value => new CountedResult(value, 1))
            .ToList();

        return EvalResult<BoundSequenceBuiltinArguments>.Ok(
            new BoundSequenceBuiltinArguments(preparedInputR.Value, iterationItems, suffixArgs));
    }

    /// <summary>MIRROR OF <see cref="ApplyBuiltinCountedSequence"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> ApplyBuiltinCountedSequenceAsync(
        BuiltinId builtin,
        SequenceBuiltinMetadata metadata,
        IReadOnlyList<ResolvedArgumentAlgorithm> args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var boundR = await BindSequenceBuiltinArgumentsAsync(builtin, metadata, args, ctx, valEnv).ConfigureAwait(false);
        if (boundR.IsError) return boundR.Error;

        var bound = boundR.Value;

        // The pure per-builtin execution helpers are shared with the synchronous twin;
        // only the callback-driven builtins (filter, map, reduce) await.
        EvalResult<CountedResult> WithPreparedFlatItems(
            Func<IReadOnlyList<Result>, EvalResult<CountedResult>> handler)
            => handler(bound.PreparedInput.FlattenedItems);

        EvalResult<CountedResult> WithPreparedNumericItems(
            Func<IReadOnlyList<Decimal128>, EvalResult<CountedResult>> handler)
        {
            var numbersR = ExpectPreparedNumericItems(builtin, bound.PreparedInput);
            if (numbersR.IsError) return numbersR.Error;

            return handler(numbersR.Value);
        }

        switch (builtin)
        {
            case BuiltinId.@filter:
                {
                    var predicateR = ExpectPreparedAlgorithmSuffixArg(
                        builtin,
                        metadata.SuffixArgs,
                        bound.SuffixArgs,
                        0);
                    if (predicateR.IsError) return predicateR.Error;

                    return await EvalFilterCountedAsync(bound.IterationItems, predicateR.Value, ctx, valEnv).ConfigureAwait(false);
                }

            case BuiltinId.@map:
                {
                    var transformR = ExpectPreparedAlgorithmSuffixArg(
                        builtin,
                        metadata.SuffixArgs,
                        bound.SuffixArgs,
                        0);
                    if (transformR.IsError) return transformR.Error;

                    return await EvalMapCountedAsync(bound.IterationItems, transformR.Value, ctx, valEnv).ConfigureAwait(false);
                }

            case BuiltinId.@order:
                return WithPreparedNumericItems(numbers => EvalOrderCounted(ctx, numbers));
            case BuiltinId.@orderDesc:
                return WithPreparedNumericItems(numbers => EvalOrderDescCounted(ctx, numbers));
            case BuiltinId.@count:
                return WithPreparedFlatItems(EvalCountCounted);

            case BuiltinId.@contains:
                {
                    var searchedItemR = ExpectPreparedValueSuffixArg(
                        builtin,
                        metadata.SuffixArgs,
                        bound.SuffixArgs,
                        0);
                    if (searchedItemR.IsError) return searchedItemR.Error;

                    return WithPreparedFlatItems(items => EvalContainsCounted(items, searchedItemR.Value));
                }

            case BuiltinId.@distinct:
                return WithPreparedFlatItems(items => EvalDistinctCounted(ctx, items));
            case BuiltinId.@first:
                return WithPreparedFlatItems(EvalFirstCounted);
            case BuiltinId.@last:
                return WithPreparedFlatItems(EvalLastCounted);

            case BuiltinId.@take:
                {
                    var countR = ExpectPreparedWholeNumberSuffixArg(
                        builtin,
                        metadata.SuffixArgs,
                        bound.SuffixArgs,
                        0);
                    if (countR.IsError) return countR.Error;

                    return WithPreparedFlatItems(items => EvalTakeCounted(ctx, items, countR.Value));
                }

            case BuiltinId.@skip:
                {
                    var countR = ExpectPreparedWholeNumberSuffixArg(
                        builtin,
                        metadata.SuffixArgs,
                        bound.SuffixArgs,
                        0);
                    if (countR.IsError) return countR.Error;

                    return WithPreparedFlatItems(items => EvalSkipCounted(ctx, items, countR.Value));
                }

            case BuiltinId.@min:
                return WithPreparedNumericItems(EvalMinCounted);
            case BuiltinId.@max:
                return WithPreparedNumericItems(EvalMaxCounted);
            case BuiltinId.@sum:
                return WithPreparedNumericItems(EvalSumCounted);
            case BuiltinId.@avg:
                return WithPreparedNumericItems(EvalAvgCounted);

            case BuiltinId.@reduce:
                {
                    var stepR = ExpectPreparedAlgorithmSuffixArg(
                        builtin,
                        metadata.SuffixArgs,
                        bound.SuffixArgs,
                        0);
                    if (stepR.IsError) return stepR.Error;

                    var initialR = ExpectPreparedAlgorithmSuffixArgFull(
                        builtin,
                        metadata.SuffixArgs,
                        bound.SuffixArgs,
                        1);
                    if (initialR.IsError) return initialR.Error;

                    return await EvalReduceCountedAsync(
                        bound.IterationItems,
                        stepR.Value,
                        initialR.Value.AlgorithmValue,
                        initialR.Value.PreparedValue,
                        ctx,
                        valEnv).ConfigureAwait(false);
                }

            default:
                return WrongBuiltinArity(builtin, args.Count);
        }
    }

    // ── Callback twins ──────────────────────────────────────────────────────

    /// <summary>MIRROR OF <see cref="EvalResolvedCallbackCallCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalResolvedCallbackCallCountedAsync(
        Algorithm callee,
        IReadOnlyList<CountedResult> args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        string calleeName = "conditional")
    {
        // Charged dynamic invocation boundary — the single callback dispatch chokepoint.
        if (ctx.Budget.TryEnterInvocation() is { } limitError)
            return limitError;

        try
        {
            return await EvalResolvedCallbackCallCountedCoreAsync(callee, args, ctx, valEnv, calleeName).ConfigureAwait(false);
        }
        finally
        {
            ctx.Budget.ExitInvocation();
        }
    }

    /// <summary>MIRROR OF <see cref="EvalResolvedCallbackCallCountedCore"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalResolvedCallbackCallCountedCoreAsync(
        Algorithm callee,
        IReadOnlyList<CountedResult> args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        string calleeName)
    {
        switch (callee)
        {
            case Algorithm.Builtin(var builtin):
                return await ApplyBuiltinCountedResolvedAsync(
                    builtin,
                    args.Select(static arg => new ResolvedArgumentAlgorithm(
                        Algorithm: null,
                        SpreadsSequence: false)
                    {
                        PreparedValue = arg,
                    }).ToList(),
                    ctx,
                    valEnv).ConfigureAwait(false);

            case Algorithm.Conditional:
                if (TryGetFlatBinderUserEquivalent(callee) is { } simpleCallee)
                {
                    if (simpleCallee.Output.Count == 0)
                        return new EvalError.MissingOutput();

                    var countedEnvR = BindCountedCallbackParams(simpleCallee.Params, args);
                    if (countedEnvR.IsError)
                        return AttachImplicitParameterProvenance(countedEnvR.Error, simpleCallee);

                    var newCtx = WithCountedParameterEnvironments(ctx, countedEnvR.Value, simpleCallee.Params);
                    return await EvalAlgOutputCountedCoreAsync(simpleCallee, newCtx, valEnv).ConfigureAwait(false);
                }

                return await EvalConditionalCallbackCallCountedAsync(callee, args, ctx, valEnv, calleeName).ConfigureAwait(false);

            default:
                {
                    if (callee.Output.Count == 0)
                        return new EvalError.MissingOutput();

                    if (UsesPatternBinding(callee))
                    {
                        var countedPatternEnvR = BindCountedParameterPatternList(
                            callee.ParameterPatterns,
                            args,
                            ctx,
                            (required, actual) => new EvalError.ArityMismatch(required, actual));
                        if (countedPatternEnvR.IsError)
                            return AttachImplicitParameterProvenance(countedPatternEnvR.Error, callee);

                        var patternBindings = countedPatternEnvR.Value;
                        var patternCtx = WithCountedParameterEnvironments(
                            ctx,
                            patternBindings.CountedBindings,
                            patternBindings.CountedBindings.Select(static binding => binding.Item1));
                        return await EvalAlgOutputCountedCoreAsync(callee, patternCtx, valEnv).ConfigureAwait(false);
                    }

                    // Flat collecting-parameter callback binding — see the synchronous twin.
                    if (ParameterPattern.HasCollectingCaptureAtCurrentLevel(callee.ParameterPatterns))
                    {
                        var collectingPatternEnvR = BindCountedCallbackParameterPatternList(callee.ParameterPatterns, args, ctx);
                        if (collectingPatternEnvR.IsError)
                            return AttachImplicitParameterProvenance(collectingPatternEnvR.Error, callee);

                        var collectingBindings = collectingPatternEnvR.Value;
                        var collectingCtx = WithCountedParameterEnvironments(
                            ctx,
                            collectingBindings.CountedBindings,
                            collectingBindings.CountedBindings.Select(static binding => binding.Item1));
                        return await EvalAlgOutputCountedCoreAsync(callee, collectingCtx, valEnv).ConfigureAwait(false);
                    }

                    // Fixed-only flat callback binding — see the synchronous twin.
                    var countedEnvR = BindCountedCallbackParams(callee.Params, args);
                    if (countedEnvR.IsError)
                        return AttachImplicitParameterProvenance(countedEnvR.Error, callee);

                    var newCtx = WithCountedParameterEnvironments(ctx, countedEnvR.Value, callee.Params);
                    return await EvalAlgOutputCountedCoreAsync(callee, newCtx, valEnv).ConfigureAwait(false);
                }
        }
    }

    /// <summary>MIRROR OF <see cref="EvalSequenceCallbackCallCounted"/> — keep in lock-step.</summary>
    private static ValueTask<EvalResult<CountedResult>> EvalSequenceCallbackCallCountedAsync(
        Algorithm callee,
        CountedResult item,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        string calleeName = "conditional")
        => EvalResolvedCallbackCallCountedAsync(callee, [CountedSequenceCallbackItem(item)], ctx, valEnv, calleeName);

    /// <summary>MIRROR OF <see cref="EvalConditionalCallbackCallCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalConditionalCallbackCallCountedAsync(
        Algorithm callee,
        IReadOnlyList<CountedResult> explicitArgs,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        string calleeName = "conditional")
    {
        if (callee.HasDuplicateBranchPatterns())
            return new EvalError.DuplicateBranchPattern();

        var match = MatchCountedCallBranches(callee.Branches, explicitArgs);
        if (match is null)
            return new EvalError.NoMatchingBranch(calleeName);

        var (branch, bindings) = match.Value;
        var wiredBody = ChildOf(callee, branch.Body);
        var newCtx = WithCountedParameterEnvironments(
            ctx.Push(callee),
            bindings,
            bindings.Select(static binding => binding.Item1));
        var newEnv = Concat(bindings.Select(static binding => (binding.Item1, binding.Item2.Value)).ToList(), valEnv);
        return await EvalAlgOutputCountedCoreAsync(wiredBody, newCtx, newEnv).ConfigureAwait(false);
    }

    /// <summary>MIRROR OF <see cref="EvalReducerAccumulatorCollectingCallbackCallCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalReducerAccumulatorCollectingCallbackCallCountedAsync(
        Algorithm.User callee,
        IReadOnlyList<CountedResult> args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        // Charged dynamic invocation boundary — dispatched INSTEAD of the ordinary
        // callback chokepoint, so one reduce step stays one charged invocation.
        if (ctx.Budget.TryEnterInvocation() is { } limitError)
            return limitError;

        try
        {
            return await EvalReducerAccumulatorCollectingCallbackCallCountedCoreAsync(callee, args, ctx, valEnv).ConfigureAwait(false);
        }
        finally
        {
            ctx.Budget.ExitInvocation();
        }
    }

    /// <summary>MIRROR OF <see cref="EvalReducerAccumulatorCollectingCallbackCallCountedCore"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalReducerAccumulatorCollectingCallbackCallCountedCoreAsync(
        Algorithm.User callee,
        IReadOnlyList<CountedResult> args,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (callee.Output.Count == 0)
            return new EvalError.MissingOutput();

        var countedPatternEnvR = BindCountedParameterPatternList(
            callee.ParameterPatterns,
            args,
            ctx,
            (required, actual) => new EvalError.ArityMismatch(required, actual));
        if (countedPatternEnvR.IsError)
            return AttachImplicitParameterProvenance(countedPatternEnvR.Error, callee);

        var patternBindings = countedPatternEnvR.Value;
        var callbackCtx = WithCountedParameterEnvironments(
            ctx,
            patternBindings.CountedBindings,
            patternBindings.CountedBindings.Select(static binding => binding.Item1));
        return await EvalAlgOutputCountedCoreAsync(callee, callbackCtx, valEnv).ConfigureAwait(false);
    }

    /// <summary>MIRROR OF <see cref="EvalSequenceReduceStepCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalSequenceReduceStepCountedAsync(
        Algorithm callee,
        CountedResult element,
        Result accumulator,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        string calleeName = "conditional")
    {
        var elementArg = CountedSequenceCallbackItem(element);
        if (callee is Algorithm.User userReducer && ReducerAccumulatorSideHasTopLevelCollecting(userReducer))
        {
            var accumulatorSlots = accumulator.ToItems();
            var args = new List<CountedResult>(1 + accumulatorSlots.Count) { elementArg };
            foreach (var slot in accumulatorSlots)
                args.Add(new CountedResult(slot, slot.ValueCount()));

            return await EvalReducerAccumulatorCollectingCallbackCallCountedAsync(userReducer, args, ctx, valEnv).ConfigureAwait(false);
        }

        return await EvalResolvedCallbackCallCountedAsync(
            callee,
            [elementArg, new CountedResult(accumulator, accumulator.ValueCount())],
            ctx,
            valEnv,
            calleeName).ConfigureAwait(false);
    }

    // ── map/filter/reduce twins ─────────────────────────────────────────────

    /// <summary>MIRROR OF <see cref="EvalReduceCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalReduceCountedAsync(
        IReadOnlyList<CountedResult> items,
        Algorithm stepAlg,
        Algorithm initialAlg,
        CountedResult? preparedInitial,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var initialR = preparedInitial is { } preparedValue
            ? EvalResult<CountedResult>.Ok(preparedValue)
            : await EvalArgumentAlgOutputCountedAsync(initialAlg, ctx, valEnv).ConfigureAwait(false);
        if (initialR.IsError)
        {
            if (IsLikelyUnevaluatedParameterError(initialAlg, initialR.Error))
                return ReduceInitialAccumulatorRequiresValueError(initialAlg);

            return initialR.Error;
        }

        // The initial accumulator expression occupies ONE written accumulator slot —
        // see the synchronous twin.
        var accumulator = ReCountValueBoundary(initialR.Value);
        foreach (var item in items)
        {
            var stepR = WithCtx(
                "while evaluating reduce step (reduce passes each iterated collection item as collected; a collecting parameter collects supplied values as one exact list, nested sequence and list values stay intact, and top-level collecting accumulator parameters receive state slots)",
                await EvalSequenceReduceStepCountedAsync(stepAlg, item, accumulator.Value, ctx, valEnv, "reduce step").ConfigureAwait(false));
            if (stepR.IsError) return stepR.Error;

            var nextR = ExpectSingleAccumulator(stepR.Value);
            if (nextR.IsError) return nextR.Error;

            accumulator = new CountedResult(nextR.Value, 1);
        }

        return EvalResult<CountedResult>.Ok(accumulator);
    }

    /// <summary>MIRROR OF <see cref="EvalFilterCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalFilterCountedAsync(
        IReadOnlyList<CountedResult> items,
        Algorithm predicateAlg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var kept = new List<Result>();
        for (var index = 0; index < items.Count; index++)
        {
            var item = items[index];
            var truthR = await EvalFilterPredicateTruthAsync(predicateAlg, item, index, ctx, valEnv).ConfigureAwait(false);
            if (truthR.IsError)
                return truthR.Error;

            if (truthR.Value)
                kept.Add(item.Value);
        }

        return MakeCollectionListResult(ctx, kept);
    }

    /// <summary>
    /// MIRROR OF <see cref="EvalFilterPredicateTruth"/> — keep in lock-step (the
    /// synchronous plain callback wrapper is the counted twin's value projection).
    /// </summary>
    private static async ValueTask<EvalResult<bool>> EvalFilterPredicateTruthAsync(
        Algorithm predicateAlg,
        CountedResult item,
        int index,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var predicateCountedR = await EvalSequenceCallbackCallCountedAsync(
            predicateAlg, item, ctx, valEnv, "filter predicate").ConfigureAwait(false);
        var predicateR = WithFilterItemCtx(
            item.Value,
            index,
            ctx,
            predicateCountedR.IsError
                ? EvalResult<Result>.Err(predicateCountedR.Error)
                : EvalResult<Result>.Ok(predicateCountedR.Value.Value));
        if (predicateR.IsError)
            return predicateR.Error;

        var truth = predicateR.Value.SingleAtomicTruthValue();
        if (truth is null)
        {
            return new EvalError.WithContext(
                "filter predicate must return exactly one atomic numeric value",
                new EvalError.BadArity());
        }

        return EvalResult<bool>.Ok(truth.Value);
    }

    /// <summary>MIRROR OF <see cref="EvalMapCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalMapCountedAsync(
        IReadOnlyList<CountedResult> items,
        Algorithm transformAlg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var mapped = new List<Result>(items.Count);
        foreach (var item in items)
        {
            var transformR = WithCtx(
                "while evaluating map transform (map passes each iterated collection item as collected; a collecting parameter collects supplied values as one exact list and nested sequence and list values stay intact)",
                await EvalSequenceCallbackCallCountedAsync(transformAlg, item, ctx, valEnv, "map transform").ConfigureAwait(false));
            if (transformR.IsError) return transformR.Error;

            var mappedElementR = ExpectSingleMappedElement(transformR.Value);
            if (mappedElementR.IsError) return mappedElementR.Error;

            mapped.Add(mappedElementR.Value);
        }

        return MakeCollectionListResult(ctx, mapped);
    }

    // ── Loop twins ──────────────────────────────────────────────────────────

    /// <summary>
    /// MIRROR OF <see cref="WhileLoopCounted"/> — keep in lock-step. The async root
    /// context pins loop optimization off, so this twin mirrors exactly the branch the
    /// synchronous code takes under that same context (generic strategy, with the same
    /// diagnostics records); the guard makes any pinning violation loud.
    /// </summary>
    private static async ValueTask<EvalResult<CountedResult>> WhileLoopCountedAsync(
        Algorithm step,
        IReadOnlyList<Result> initialStateSlots,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        ThrowIfAsyncStrategyPinningViolated(ctx);

        ctx.LoopDiagnostics?.RecordLoopExecution();
        ctx.LoopDiagnostics?.RecordOptimizedLoopFallback("loop optimization disabled");
        return await WhileLoopGenericCountedAsync(step, initialStateSlots, ctx, valEnv).ConfigureAwait(false);
    }

    /// <summary>MIRROR OF <see cref="WhileLoopGenericCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> WhileLoopGenericCountedAsync(
        Algorithm step,
        IReadOnlyList<Result> initialStateSlots,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        // Loop-invariant step preparation, once per loop invocation — the SAME shared
        // non-evaluating helper as the synchronous twin (nothing here awaits).
        var prepared = PrepareGenericLoopStep(step, ctx);
        var stateSlots = initialStateSlots.ToList();
        while (true)
        {
            var outputSlotsR = await RunStepSlotsAsync(step, ctx, valEnv, stateSlots, "while", prepared).ConfigureAwait(false);
            if (outputSlotsR.IsError) return outputSlotsR.Error;
            var splitR = SplitContSlots(outputSlotsR.Value);
            if (splitR.IsError) return splitR.Error;
            var (nextStateSlots, cont) = splitR.Value;
            if (cont == 0) return MakeCheckedLoopStateResult(ctx, stateSlots);
            stateSlots = nextStateSlots.ToList();
        }
    }

    /// <summary>MIRROR OF <see cref="RepeatLoopCounted"/> — keep in lock-step (see <see cref="WhileLoopCountedAsync"/> on the strategy pinning).</summary>
    private static async ValueTask<EvalResult<CountedResult>> RepeatLoopCountedAsync(
        Algorithm step,
        long count,
        IReadOnlyList<Result> initialStateSlots,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        ThrowIfAsyncStrategyPinningViolated(ctx);

        ctx.LoopDiagnostics?.RecordLoopExecution();

        if (count == 0)
            return MakeCheckedLoopStateResult(ctx, initialStateSlots);

        ctx.LoopDiagnostics?.RecordOptimizedLoopFallback("loop optimization disabled");
        return await RepeatLoopGenericCountedAsync(step, count, initialStateSlots, ctx, valEnv).ConfigureAwait(false);
    }

    /// <summary>MIRROR OF <see cref="RepeatLoopGenericCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> RepeatLoopGenericCountedAsync(
        Algorithm step,
        long count,
        IReadOnlyList<Result> initialStateSlots,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var stateSlots = initialStateSlots.ToList();
        // Zero-iteration guard mirrors the synchronous twin: no step preparation for a
        // loop that never binds its step.
        if (count <= 0)
            return MakeCheckedLoopStateResult(ctx, stateSlots);

        var prepared = PrepareGenericLoopStep(step, ctx);
        for (var k = 0; k < count; k++)
        {
            var outputSlotsR = await RunStepSlotsAsync(step, ctx, valEnv, stateSlots, "repeat", prepared).ConfigureAwait(false);
            if (outputSlotsR.IsError) return outputSlotsR.Error;
            stateSlots = outputSlotsR.Value.ToList();
        }
        return MakeCheckedLoopStateResult(ctx, stateSlots);
    }

    /// <summary>MIRROR OF <see cref="RunStepSlots"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<IReadOnlyList<Result>>> RunStepSlotsAsync(
        Algorithm step,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv,
        IReadOnlyList<Result> stateSlots,
        string loopName,
        PreparedGenericLoopStep prepared)
    {
        // One loop ITERATION is one charged work unit — identical chokepoint to the
        // synchronous twin.
        if (ctx.Budget.TryChargeStep() is { } limitError)
            return limitError;

        var boundR = BindLoopStepState(
            prepared.BindingContract,
            stateSlots,
            ctx,
            loopName,
            prepared.BindingSelection);
        if (boundR.IsError) return boundR.Error;

        // Fresh concatenation per iteration for the same cache-identity reason as the
        // synchronous twin.
        var stepCtx = ctx
            .WithCountedParamEnv(Concat(boundR.Value.CountedBindings, prepared.ShadowedCountedParamEnv));
        return await EvalAlgOutputSlotsAsync(
            step,
            stepCtx,
            Concat(boundR.Value.ValueBindings, valEnv),
            preserveSequenceSpreadExpressionBoundaries: prepared.PreserveSequenceSpreadExpressionBoundaries).ConfigureAwait(false);
    }

    // ── Dot-call twins ──────────────────────────────────────────────────────

    /// <summary>
    /// MIRROR OF <see cref="EvalDotCallCounted"/> — keep in lock-step. The sequence
    /// pipeline attempt is omitted under the async strategy pinning (see
    /// <see cref="ThrowIfAsyncStrategyPinningViolated"/>).
    /// </summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalDotCallCountedAsync(
        Expr.DotCall dotCall,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        ThrowIfAsyncStrategyPinningViolated(ctx);

        var target = dotCall.Target;
        var name = dotCall.Name;
        var argsOpt = dotCall.Args;

        var targetResult = ResolveAlg(target, ctx);
        if (targetResult.IsError)
        {
            if (targetResult.Error is EvalError.NotAnAlgorithm)
            {
                if (dotCall.UsesOrdinaryDotStringIntrinsic())
                {
                    // The synchronous twin evaluates the value-only target with plain
                    // Eval; the counted twin's value projection is the same value.
                    var valCountedR = await EvalCountedAsync(target, ctx, valEnv).ConfigureAwait(false);
                    if (valCountedR.IsError) return valCountedR.Error;
                    var outR = ResultToString(ctx, valCountedR.Value.Value);
                    if (outR.IsError) return outR.Error;
                    return EvalResult<CountedResult>.Ok(new CountedResult(outR.Value, outR.Value.ValueCount()));
                }
                return await CallLexicalWithReceiverCountedAsync(dotCall, ctx, valEnv).ConfigureAwait(false);
            }

            return targetResult.Error;
        }

        var targetAlg = targetResult.Value;

        if (dotCall.UsesOrdinaryDotStringIntrinsic())
        {
            var val = await EvalDotStringReceiverAlgOutputAsync(target, targetAlg, ctx, valEnv).ConfigureAwait(false);
            if (val.IsError) return val.Error;
            var outR = ResultToString(ctx, val.Value);
            if (outR.IsError) return outR.Error;
            return EvalResult<CountedResult>.Ok(new CountedResult(outR.Value, outR.Value.ValueCount()));
        }

        var prop = LookupPropBinding(targetAlg, name);
        if (prop is not null)
        {
            if (!IsExported(prop))
                return new EvalError.LocalOnlyProperty(OpenExprName(target), name, prop.Exposure);

            var wired = ChildOf(targetAlg, prop.Value);
            if (argsOpt is null)
            {
                var simpleCallee = TryGetFlatBinderUserEquivalent(wired);
                if (simpleCallee is not null)
                    return new EvalError.ArityMismatch(simpleCallee.Params.Count, 0);

                if (wired is Algorithm.Conditional)
                    return new EvalError.NoMatchingBranch(name);

                if (wired.Params.Count == 0)
                    return ReCountValueBoundary(
                        await EvalZeroArgPropertyAccessCountedAsync(
                            targetAlg, prop, ZeroArgPropertyAccessKind.CountedStructural, wired, ctx, valEnv).ConfigureAwait(false));
                return ZeroArgumentDemandArityMismatch(wired);
            }

            return await EvalResolvedCallCountedAsync(
                wired,
                argsOpt,
                ctx,
                valEnv,
                CallDiagnosticName.FromKnown(name)).ConfigureAwait(false);
        }

        if (targetAlg.DefinesConditionalBranchProperty(name))
            return new EvalError.LocalOnlyProperty(OpenExprName(target), name, PropertyExposure.LocalOnlyConditionalAlgorithm);

        return await CallLexicalWithReceiverCountedAsync(dotCall, ctx, valEnv).ConfigureAwait(false);
    }

    /// <summary>MIRROR OF <see cref="CallLexicalWithReceiverCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> CallLexicalWithReceiverCountedAsync(
        Expr.DotCall dotCall,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        // Stored-fallback consumption — see CallLexicalWithReceiverCounted.
        if (dotCall.EffectiveLexicalFallback is not Expr.Resolve(var fallbackName))
            return await CallLexicalFallbackCalleeWithReceiverCountedAsync(dotCall, ctx, valEnv).ConfigureAwait(false);

        var sequenceDotCallR = await TryBuildSequenceBuiltinDotCallAsync(fallbackName, dotCall.Target, dotCall.Args, ctx, valEnv).ConfigureAwait(false);
        if (sequenceDotCallR.IsError) return sequenceDotCallR.Error;
        if (sequenceDotCallR.Value is { } sequenceDotCall)
            return await ApplyBuiltinCountedResolvedAsync(sequenceDotCall.Builtin, sequenceDotCall.Args, ctx, valEnv).ConfigureAwait(false);

        var calleeR = ResolveNamedAlgorithm(fallbackName, span: null, ctx);
        if (calleeR.IsError) return calleeR.Error;
        var combinedArgs = BuildLexicalReceiverCallArgs(dotCall.Target, dotCall.Args);
        return await EvalResolvedCallCountedAsync(
            calleeR.Value,
            combinedArgs,
            ctx,
            valEnv,
            CallDiagnosticName.FromKnown(fallbackName),
            CallArgumentAssembly.InjectedDotReceiverLeading).ConfigureAwait(false);
    }

    /// <summary>
    /// MIRROR OF <see cref="CallLexicalFallbackCalleeWithReceiverCounted"/> — keep in
    /// lock-step. (The synchronous twin's NoInlining attribute serves the native
    /// stack-margin calibration of the recursive dot-chain frame; an async twin's logic
    /// lives in its state machine's MoveNext and is not subject to that inlining
    /// concern.)
    /// </summary>
    private static async ValueTask<EvalResult<CountedResult>> CallLexicalFallbackCalleeWithReceiverCountedAsync(
        Expr.DotCall dotCall,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var calleeR = ResolveAlg(dotCall.EffectiveLexicalFallback, ctx);
        if (calleeR.IsError) return calleeR.Error;
        return await EvalResolvedCallCountedAsync(
            calleeR.Value,
            BuildLexicalReceiverCallArgs(dotCall.Target, dotCall.Args),
            ctx,
            valEnv,
            CallDiagnosticName.FromKnown(dotCall.Name),
            CallArgumentAssembly.InjectedDotReceiverLeading).ConfigureAwait(false);
    }

    /// <summary>MIRROR OF <see cref="TryBuildSequenceBuiltinDotCall"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<SequenceBuiltinDotCall?>> TryBuildSequenceBuiltinDotCallAsync(
        string name,
        Expr receiver,
        OutputBundle? extraArgs,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var calleeR = ResolveNamedAlgorithm(name, span: null, ctx);
        if (calleeR.IsError
            || calleeR.Value is not Algorithm.Builtin(var builtin)
            || GetSequenceBuiltinMetadata(builtin) is null)
        {
            return EvalResult<SequenceBuiltinDotCall?>.Ok(null);
        }

        var receiverArgAlgsR = await SequenceBuiltinDotReceiverArgsAsync(receiver, ctx, valEnv).ConfigureAwait(false);
        if (receiverArgAlgsR.IsError) return receiverArgAlgsR.Error;

        var argAlgs = new List<ResolvedArgumentAlgorithm>(receiverArgAlgsR.Value);

        if (extraArgs is not null)
        {
            var extraArgAlgsR = ResolveArgAlgsWithSequenceSpread(extraArgs, ctx, valEnv);
            if (extraArgAlgsR.IsError) return extraArgAlgsR.Error;
            if (builtin == BuiltinId.@reduce
                && extraArgAlgsR.Value is [{ Algorithm: { Params.Count: > 0 } reducerAlgorithm }])
            {
                return ReduceInitialAccumulatorRequiresValueError(reducerAlgorithm);
            }

            argAlgs.AddRange(extraArgAlgsR.Value);
        }

        return EvalResult<SequenceBuiltinDotCall?>.Ok(
            new SequenceBuiltinDotCall(builtin, argAlgs));
    }

    /// <summary>MIRROR OF <see cref="SequenceBuiltinDotReceiverArgs"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<IReadOnlyList<ResolvedArgumentAlgorithm>>> SequenceBuiltinDotReceiverArgsAsync(
        Expr receiver,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var receiverR = await EvalSequenceBuiltinDotReceiverCountedAsync(receiver, ctx, valEnv).ConfigureAwait(false);
        if (receiverR.IsError) return receiverR.Error;

        // Prepared-value-only carry — see the synchronous twin.
        return EvalResult<IReadOnlyList<ResolvedArgumentAlgorithm>>.Ok(
            [new ResolvedArgumentAlgorithm(Algorithm: null, SpreadsSequence: false)
            {
                PreparedValue = receiverR.Value,
            }]);
    }

    /// <summary>MIRROR OF <see cref="EvalSequenceBuiltinDotReceiverCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalSequenceBuiltinDotReceiverCountedAsync(
        Expr receiver,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        // The receiver is this builtin call's collection ARGUMENT and consumes one
        // depth-only argument-evaluation level — identical protocol to the synchronous twin.
        if (ctx.Budget.TryEnterArgumentEvaluation() is { } limitError)
            return limitError;
        try
        {
            // The synchronous twin evaluates with plain Eval and re-counts to
            // ValueCount; the counted twin's value projection is the same value.
            var valueCountedR = await EvalCountedAsync(receiver, ctx, valEnv).ConfigureAwait(false);
            return valueCountedR.IsError
                ? valueCountedR.Error
                : EvalResult<CountedResult>.Ok(new CountedResult(valueCountedR.Value.Value, valueCountedR.Value.Value.ValueCount()));
        }
        finally
        {
            ctx.Budget.ExitInvocation();
        }
    }

    /// <summary>MIRROR OF <see cref="EvalDotStringReceiverAlgOutput"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<Result>> EvalDotStringReceiverAlgOutputAsync(
        Expr target,
        Algorithm targetAlg,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        switch (target)
        {
            case Expr.Param(var name):
                if (LookupAlgBinding(ctx.AlgEnv, name) is { ValueError: { } stickyLimit })
                    return AtSpanIfMissing(stickyLimit, target.Span);
                return await EvalResolvedAlgOutputForValueDemandAsync(targetAlg, ctx, valEnv).ConfigureAwait(false);

            case Expr.Resolve:
                return await EvalResolvedAlgOutputForValueDemandAsync(targetAlg, ctx, valEnv).ConfigureAwait(false);

            default:
                return await EvalAlgOutputValueAsync(targetAlg, ctx, valEnv).ConfigureAwait(false);
        }
    }

    // ── Sequence-join twins ─────────────────────────────────────────────────

    /// <summary>MIRROR OF <see cref="EvalSequenceConstructCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalSequenceConstructCountedAsync(
        Expr expr,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var leaves = SequenceConstructLeaves(expr);
        var items = new List<Result>(leaves.Count);

        foreach (var leaf in leaves)
        {
            if (leaf is Expr.SequenceSpread)
            {
                var suppliedItemsR = await EvalSequenceSpreadOperandItemsAsync(leaf, ctx, valEnv).ConfigureAwait(false);
                if (suppliedItemsR.IsError) return suppliedItemsR.Error;

                items.AddRange(suppliedItemsR.Value);
                continue;
            }

            // The synchronous twin evaluates the leaf with plain Eval; the counted
            // twin's value projection is the same value.
            var valueR = await EvalCountedAsync(leaf, ctx, valEnv).ConfigureAwait(false);
            if (valueR.IsError) return valueR.Error;

            if (valueR.Value.Value.ValueCount() != 0)
                items.Add(valueR.Value.Value);
        }

        if (ReserveSequenceCapture(ctx, items.Count) is { } sequenceLimitError)
            return sequenceLimitError;

        var value = CombineOutputSlots(items);
        return EvalResult<CountedResult>.Ok(new CountedResult(
            value,
            value.ValueCount()));
    }

    /// <summary>MIRROR OF <see cref="EvalSequenceSpreadOperandItems"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<IReadOnlyList<Result>>> EvalSequenceSpreadOperandItemsAsync(
        Expr expr,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        if (expr is Expr.Capture(var captureBody))
        {
            var captureSpan = PreferExpressionSpan(expr.Span, captureBody);
            var captureR = WithSpan(captureSpan, await EvalCaptureValueAsync(captureBody, ctx, valEnv).ConfigureAwait(false));
            if (captureR.IsError)
                return IsMissingOutputError(captureR.Error)
                    ? SpreadMissingOutput(captureSpan)
                    : captureR.Error;

            return EvalResult<IReadOnlyList<Result>>.Ok(captureR.Value.SpreadItems());
        }

        if (expr is Expr.AlgorithmExpr(var alg))
        {
            var wired = WireToCaller(ctx, alg);
            var blockSpan = PreferExpressionSpan(expr.Span, wired.Output);
            if (wired.Params.Count != 0)
                return MissingImplicitArguments<IReadOnlyList<Result>>(wired, blockSpan);

            var blockR = await EvalAlgOutputValueAsync(wired, ctx, valEnv).ConfigureAwait(false);
            if (blockR.IsError)
                return IsMissingOutputError(blockR.Error)
                    ? SpreadMissingOutput(blockSpan)
                    : blockR.Error;

            return EvalResult<IReadOnlyList<Result>>.Ok(blockR.Value.SpreadItems());
        }

        // The synchronous twin evaluates the operand with plain Eval; the counted
        // twin's value projection is the same value.
        var outputR = await EvalCountedAsync(expr, ctx, valEnv).ConfigureAwait(false);
        if (outputR.IsError)
            return IsMissingOutputError(outputR.Error)
                ? SpreadMissingOutput(expr.Span)
                : outputR.Error;

        return EvalResult<IReadOnlyList<Result>>.Ok(outputR.Value.Value.SpreadItems());
    }

    /// <summary>MIRROR OF <see cref="EvalSequenceSpreadCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalSequenceSpreadCountedAsync(
        Expr expr,
        EvalCtx ctx,
        IReadOnlyList<(string, Result)> valEnv)
    {
        var operand = expr;
        var layers = 0;
        while (operand is Expr.SequenceSpread(var supplied))
        {
            operand = supplied;
            layers++;
        }

        var operandR = await EvalSequenceSpreadOperandItemsAsync(operand, ctx, valEnv).ConfigureAwait(false);
        if (operandR.IsError) return operandR.Error;

        var items = operandR.Value;
        for (var layer = 0; layer < layers; layer++)
        {
            var capturedR = MakeCheckedSequenceCapture(ctx, items, expr.Span);
            if (capturedR.IsError) return capturedR.Error;

            if (layer == layers - 1)
                return EvalResult<CountedResult>.Ok(new CountedResult(capturedR.Value, items.Count));

            items = capturedR.Value.SpreadItems();
        }

        throw new InvalidOperationException("Sequence spread must contain at least one layer.");
    }
}
