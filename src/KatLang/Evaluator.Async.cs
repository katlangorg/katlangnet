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
/// group; the dispatch is a compiler-exhaustive switch over the closed
/// <see cref="Expr"/> hierarchy, so a new recursive variant is a build error
/// until it is given a twin case and can never silently fall through to
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
/// mirror the generic strategies. Every strategy charges every budget identically
/// (Q-09b; see <c>CreateRootCtx</c>), so results, budget accounting and limit verdicts are
/// unchanged; only internal diagnostics observations (which honestly record the generic
/// strategy) differ. The ROUTE itself is chosen by capability — an async-capable cache, an
/// asynchronous host operation, a deferred module region — never by
/// <see cref="EvaluationLimits"/>. The optimized executors can be taught to cooperate with
/// the twin family later without any architectural change.</para>
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
    /// <see cref="RunAsync(Expr, HostOperations, EvaluationLimits?, long?, CancellationToken)"/>
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
    public static Task<EvalResult<Result>> RunAsync(
        Expr expr, EvaluationLimits? limits, CancellationToken cancellationToken)
        => RunAsync(expr, limits, randomSeed: null, cancellationToken);

    /// <summary>
    /// Asynchronous counterpart of
    /// <see cref="Run(Expr, EvaluationLimits?, long?, CancellationToken)"/>: the same
    /// seed contract (a seeded run's stream is identical whether it evaluates through
    /// this entry point, the synchronous one, or the async twin path), with the
    /// synchronous-completion and cancellation notes of
    /// <see cref="RunAsync(Expr, EvaluationLimits?, CancellationToken)"/>.
    /// </summary>
    /// <exception cref="OperationCanceledException">
    /// <paramref name="cancellationToken"/> was cancelled before or during evaluation.
    /// The exception is delivered through the returned task and carries that token.
    /// </exception>
    /// <exception cref="ArgumentNullException">
    /// <paramref name="expr"/> is null. Like every exception of the asynchronous entry
    /// points, delivered through the returned task.
    /// </exception>
    public static async Task<EvalResult<Result>> RunAsync(
        Expr expr, EvaluationLimits? limits, long? randomSeed, CancellationToken cancellationToken)
    {
        ArgumentNullException.ThrowIfNull(expr);
        return await RunAsync(
            expr,
            CreateRunScopedZeroArgPropertyResultCache(expr, hostOperations: null),
            limits,
            loopDiagnostics: null,
            sequenceDiagnostics: null,
            observations: null,
            hostOperations: null,
            randomSeed,
            cancellationToken).ConfigureAwait(false);
    }

    /// <summary>
    /// Run evaluation with host operations ambiently in scope and an optional random seed
    /// (<c>null</c> for an unseeded run) — the asynchronous counterpart of
    /// <see cref="Run(Expr, HostOperations, EvaluationLimits?, long?, CancellationToken)"/>
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
    /// for the full contract). A run suspended by an incomplete host awaitable resumes with
    /// its random stream exactly where it left off: nothing is reseeded or replayed, so a
    /// seeded run produces the same KatLang random values whether or not it suspends.
    /// Host-operation results themselves are outside the seeded stream.</para>
    ///
    /// <para>Every arity of the <c>RunAsync</c> family has exactly one overload, so
    /// positional arguments — <c>null</c> literals included — always select exactly one of
    /// them: <c>RunAsync(expr, null, null, token)</c> is the four-argument limits-and-seed
    /// overload.</para>
    ///
    /// <para><b>Recursion depth on the async twin path.</b> The twin path's per-level
    /// frames are larger than the synchronous frames, so a deeply recursive program that
    /// does not suspend usually reaches the host-stack backstop — the structured
    /// <see cref="EvalError.EvaluationStackExhausted"/> — at a SHALLOWER recursion depth
    /// than the synchronous evaluator, and before the deterministic
    /// <see cref="EvaluationLimits.MaxDepth"/> verdict; one that genuinely suspends before
    /// descending resumes on a fresh stack and can go DEEPER. The outcome is always a
    /// structured resource-limit error, never a process crash; the depth depends on the host
    /// (thread, build, runtime and JIT state, platform), never on which limits are configured,
    /// and is not a language guarantee (see <see cref="EvaluationLimits.MaxDepth"/>).</para>
    /// </summary>
    /// <exception cref="ArgumentNullException">
    /// <paramref name="expr"/> is null, or <paramref name="hostOperations"/> is null — a run
    /// without host operations uses an overload that does not take them. Delivered through
    /// the returned task.
    /// </exception>
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
        long? randomSeed,
        CancellationToken cancellationToken)
    {
        ArgumentNullException.ThrowIfNull(expr);
        ArgumentNullException.ThrowIfNull(hostOperations);
        return await RunAsync(
            expr,
            CreateRunScopedZeroArgPropertyResultCache(expr, hostOperations),
            limits,
            loopDiagnostics: null,
            sequenceDiagnostics: null,
            observations: null,
            hostOperations,
            randomSeed,
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
    public static Task<EvalResult<IReadOnlyList<Decimal128>>> RunFlatAsync(
        Expr expr, EvaluationLimits? limits, CancellationToken cancellationToken)
        => RunFlatAsync(expr, limits, randomSeed: null, cancellationToken);

    /// <summary>
    /// Asynchronous counterpart of
    /// <see cref="RunFlat(Expr, EvaluationLimits?, long?, CancellationToken)"/>, with the
    /// same seed contract and the synchronous-completion and cancellation notes of
    /// <see cref="RunFlatAsync(Expr, EvaluationLimits?, CancellationToken)"/>.
    /// </summary>
    /// <exception cref="OperationCanceledException">
    /// <paramref name="cancellationToken"/> was cancelled before or during evaluation
    /// or the bounded host projection. The exception is delivered through the returned
    /// task and carries that token.
    /// </exception>
    public static async Task<EvalResult<IReadOnlyList<Decimal128>>> RunFlatAsync(
        Expr expr, EvaluationLimits? limits, long? randomSeed, CancellationToken cancellationToken)
        => ProjectFlatHostAtoms(
            await RunAsync(expr, limits, randomSeed, cancellationToken).ConfigureAwait(false),
            limits,
            cancellationToken);

    /// <summary>
    /// Asynchronous counterpart of
    /// <see cref="RunFlat(Expr, HostOperations, EvaluationLimits?, long?, CancellationToken)"/>.
    /// Incomplete host awaitables suspend evaluation. The numeric projection is bounded by
    /// the effective collection limit, and every exception is delivered through the task.
    /// </summary>
    /// <exception cref="ArgumentNullException"><paramref name="expr"/> or <paramref name="hostOperations"/> is null.</exception>
    /// <exception cref="OperationCanceledException">Evaluation or projection was cancelled.</exception>
    public static async Task<EvalResult<IReadOnlyList<Decimal128>>> RunFlatAsync(
        Expr expr, HostOperations hostOperations, EvaluationLimits? limits, long? randomSeed, CancellationToken cancellationToken)
        => ProjectFlatHostAtoms(
            await RunAsync(expr, hostOperations, limits, randomSeed, cancellationToken).ConfigureAwait(false),
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
        Expr expr,
        IZeroArgPropertyResultCache zeroArgPropertyResultCache,
        HostOperations? hostOperations)
        => zeroArgPropertyResultCache is IAsyncZeroArgPropertyResultCache
            || hostOperations?.ContainsAsynchronousOperations == true
            // B2c: a root carrying deferred module regions — materializing a selected branch
            // awaits the module downloader, the third and only other run component that can
            // complete asynchronously.
            || DeferredModuleRegion.RequiresAsyncEvaluation(expr);

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
        Expr expr,
        IZeroArgPropertyResultCache zeroArgPropertyResultCache,
        HostOperations? hostOperations)
    {
        if (zeroArgPropertyResultCache is IAsyncZeroArgPropertyResultCache)
            return;

        if (hostOperations?.ContainsAsynchronousOperations == true)
        {
            throw new InvalidOperationException(
                "Asynchronous host operations require an async-capable zero-argument property result cache " +
                "for the run; use an async evaluation entry point that constructs one.");
        }

        if (DeferredModuleRegion.RequiresAsyncEvaluation(expr))
        {
            throw new InvalidOperationException(
                "A program with deferred module regions (conditional branches whose module dependencies load " +
                "on demand) requires an async-capable zero-argument property result cache for the run; use an " +
                "async evaluation entry point that constructs one.");
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
        Expr expr,
        HostOperations? hostOperations)
        => hostOperations?.ContainsAsynchronousOperations == true
            // B2c: a root carrying deferred module regions runs on the twin path too, and
            // so pairs with the async-capable cache by the same rule.
            || DeferredModuleRegion.RequiresAsyncEvaluation(expr)
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
        long? randomSeed,
        CancellationToken cancellationToken)
    {
        ThrowIfAsyncHostOperationsWithoutAsyncCapableCache(expr, zeroArgPropertyResultCache, hostOperations);
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
            randomSeed,
            cancellationToken);
    }

    /// <summary>
    /// Internal async run: routes to the synchronous pipeline (fast path) or the async
    /// twin family, per <see cref="RequiresAsyncEvaluationPath"/>. The twin path shares
    /// the internal synchronous
    /// <see cref="Run(Expr, IZeroArgPropertyResultCache, bool, LoopOptimizationDiagnostics?, bool, SequencePipelineDiagnostics?, EvaluationLimits?, EvaluationObservations?, HostOperations?, long?, CancellationToken)"/>
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
        long? randomSeed = null,
        CancellationToken cancellationToken = default)
    {
        ArgumentNullException.ThrowIfNull(zeroArgPropertyResultCache);

        if (!RequiresAsyncEvaluationPath(expr, zeroArgPropertyResultCache, hostOperations))
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
                randomSeed,
                cancellationToken);
        }

        // Twin path: the same shared preparation as the internal synchronous Run(...);
        // only the dispatch below is twin-specific.
        var preparation = PrepareAsyncTwinRun(
            expr, zeroArgPropertyResultCache, loopDiagnostics, sequenceDiagnostics, limits, observations, hostOperations, randomSeed, cancellationToken);
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

    /// <summary>Async twin of the internal <see cref="RunCounted(Expr, IZeroArgPropertyResultCache, EvaluationLimits?, HostOperations?, long?, CancellationToken)"/>.</summary>
    internal static async ValueTask<EvalResult<CountedResult>> RunCountedAsync(
        Expr expr,
        IZeroArgPropertyResultCache zeroArgPropertyResultCache,
        EvaluationLimits? limits = null,
        HostOperations? hostOperations = null,
        long? randomSeed = null,
        CancellationToken cancellationToken = default)
    {
        ArgumentNullException.ThrowIfNull(zeroArgPropertyResultCache);

        if (!RequiresAsyncEvaluationPath(expr, zeroArgPropertyResultCache, hostOperations))
            return RunCounted(expr, zeroArgPropertyResultCache, limits, hostOperations, randomSeed, cancellationToken);

        // Twin path: the same shared preparation as RunCounted; only the dispatch
        // below is twin-specific.
        var preparation = PrepareAsyncTwinRun(
            expr, zeroArgPropertyResultCache, loopDiagnostics: null, sequenceDiagnostics: null, limits, observations: null, hostOperations, randomSeed, cancellationToken);
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
        long? randomSeed = null,
        CancellationToken cancellationToken = default)
    {
        ArgumentNullException.ThrowIfNull(zeroArgPropertyResultCache);
        ArgumentException.ThrowIfNullOrWhiteSpace(topLevelPropertyName);

        if (!RequiresAsyncEvaluationPath(expr, zeroArgPropertyResultCache, hostOperations))
            return RunCountedWithTopLevelProperty(expr, topLevelPropertyName, zeroArgPropertyResultCache, limits, hostOperations, randomSeed, cancellationToken);

        // Twin path: the same shared preparation as RunCountedWithTopLevelProperty;
        // only the dispatch below is twin-specific.
        var preparation = PrepareAsyncTwinRun(
            expr, zeroArgPropertyResultCache, loopDiagnostics: null, sequenceDiagnostics: null, limits, observations: null, hostOperations, randomSeed, cancellationToken);
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
        long? randomSeed = null,
        CancellationToken cancellationToken = default)
    {
        var cache = zeroArgPropertyResultCache
            ?? CreateRunScopedZeroArgPropertyResultCache(expr, hostOperations);
        if (!RequiresAsyncEvaluationPath(expr, cache, hostOperations))
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
                randomSeed,
                cancellationToken);
        }

        // Twin path: the same shared preparation as RunCountedObserved; only the
        // dispatch below is twin-specific.
        var preparation = PrepareAsyncTwinRun(
            expr, cache, loopDiagnostics, sequenceDiagnostics, limits, observations, hostOperations, randomSeed, cancellationToken);
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
        if (AcceptsZeroSuppliedArguments(wired))
        {
            var countedR = await EvalZeroArgumentDemandOutputCountedAsync(wired, ctx, []).ConfigureAwait(false);
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
        if (AcceptsZeroSuppliedArguments(wired))
        {
            var result = await EvalZeroArgumentDemandOutputCountedAsync(wired, ctx, []).ConfigureAwait(false);
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
        if (!AcceptsZeroSuppliedArguments(wired))
        {
            var blockSpan = span ?? FirstSpan(wired.Output);
            return MissingImplicitArguments<CountedRootProgramResult>(wired, blockSpan);
        }

        var outputR = await EvalZeroArgumentDemandOutputCountedAsync(wired, ctx, []).ConfigureAwait(false);
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
        ValEnv valEnv)
    {
        var binding = LookupPropBinding(alg, name, ctx.Budget);
        if (binding is null)
            return EvalResult<CountedResult?>.Ok(null);

        // An alias binding is read as its target, keyed by its own binding.
        var resolvedR = NormalizeTopLevelBinding(binding, ChildOf(alg, binding.Value), ctx);
        if (resolvedR.IsError)
            return resolvedR.Error;
        var resolvedAlgorithm = resolvedR.Value;
        var span = binding.FirstDeclarationSpan;
        // A named top-level property read is an ordinary zero-argument value demand, so
        // the ONE law decides and shapes its report: a callable that cannot accept zero
        // supplied arguments is the property-context mismatch naming its true minimum
        // supply, and a clause family keeps its ordinary dispatch failure.
        if (ZeroArgumentValueDemandRejection(ZeroArgumentDemandShape.Property, name, span, resolvedAlgorithm) is { } rejection)
            return rejection;

        var propertyR = WithPropertyContextOnMissingOutput(
            name,
            span,
            resolvedAlgorithm,
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
    /// MIRROR OF <see cref="EvalParamCounted"/> — identical by construction. A parameter
    /// read evaluates NOTHING: its value outcome — the bound value, or the failure its
    /// written argument slot's one value evaluation established — was fixed at argument
    /// assembly (AT-MOST-ONCE ARGUMENT VALUE EVALUATION), so the read has no child
    /// evaluation to route through the async seam and never suspends.
    /// </summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalParamCountedAsync(
        string name,
        SourceSpan? span,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        ctx = ParameterContext(name, ctx, ref valEnv);
        return LookupNeed(ctx.NeedEnv, name) is { } need
            ? DemandParameter(need, await need.DemandAsync().ConfigureAwait(false), name, span)
            : EvalParamCounted(name, span, ctx, valEnv);
    }

    /// <summary>MIRROR OF <see cref="LookupNativeArgument"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<Result>> LookupNativeArgumentAsync(
        EvalCtx ctx,
        ValEnv valEnv,
        string name)
        => ProjectCountedValue(await EvalParamCountedAsync(name, span: null, ctx, valEnv).ConfigureAwait(false));

    /// <summary>MIRROR OF <see cref="CollectMathNativeArguments"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<Decimal128[]>> CollectMathNativeArgumentsAsync(
        IReadOnlyList<string> argNames,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        var args = new Decimal128[argNames.Count];
        for (var i = 0; i < argNames.Count; i++)
        {
            var valR = await LookupNativeArgumentAsync(ctx, valEnv, argNames[i]).ConfigureAwait(false);
            if (valR.IsError) return valR.Error;
            // MIRROR of CollectMathNativeArguments: the ONE numeric coercion.
            var numR = ExpectInt(valR.Value);
            if (numR.IsError) return numR.Error;
            args[i] = numR.Value;
        }

        return EvalResult<Decimal128[]>.Ok(args);
    }

    /// <summary>MIRROR OF <see cref="CollectHostOperationArguments"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<IReadOnlyList<Result>>> CollectHostOperationArgumentsAsync(
        IReadOnlyList<string> argNames,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        if (argNames.Count == 0)
            return EvalResult<IReadOnlyList<Result>>.Ok([]);

        var arguments = new Result[argNames.Count];
        for (var i = 0; i < argNames.Count; i++)
        {
            var valueR = await LookupNativeArgumentAsync(ctx, valEnv, argNames[i]).ConfigureAwait(false);
            if (valueR.IsError) return valueR.Error;
            arguments[i] = valueR.Value;
        }

        return EvalResult<IReadOnlyList<Result>>.Ok(Array.AsReadOnly(arguments));
    }

    /// <summary>MIRROR OF <see cref="InvokeSynchronousHostOperation"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<Result>> InvokeSynchronousHostOperationAsync(
        HostOperation hostOperation,
        IReadOnlyList<string> argNames,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        if (hostOperation.SynchronousImplementation is not { } implementation)
        {
            throw new InvalidOperationException(
                $"Asynchronous host operation '{hostOperation.Name}' reached the synchronous evaluator; " +
                "async host configurations must route through the async evaluation path.");
        }

        if (ValidateHostOperationNativeSignature(hostOperation, argNames) is { } signatureError)
            return signatureError;

        var argumentsR = await CollectHostOperationArgumentsAsync(argNames, ctx, valEnv).ConfigureAwait(false);
        if (argumentsR.IsError) return argumentsR.Error;

        var value = implementation(argumentsR.Value, ctx.Budget.CancellationToken);
        return EvalResult<Result>.Ok(NormalizeHostOperationValue(hostOperation, value));
    }

    /// <summary>
    /// MIRROR OF <see cref="EvalNativeCall"/> — keep in lock-step. Only the
    /// declared-argument reads are awaited; the member computation itself is the
    /// SHARED <see cref="ApplyMathNative"/> over the SAME run stream
    /// (<c>ctx.Budget.RandomSource</c>), so neither the native member set nor the
    /// random draw order can drift between the two paths — a suspension before this
    /// point resumes with the stream where it left off, never reseeded or replayed.
    /// Asynchronous host operations never reach here — <see cref="EvalCountedAsync"/>
    /// intercepts them at their own await site.
    /// </summary>
    private static async ValueTask<EvalResult<Result>> EvalNativeCallAsync(
        string fnName,
        IReadOnlyList<string> argNames,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        if (ctx.Budget.HostOperations is { } hostOperations
            && fnName.StartsWith(HostOperations.NativeNamePrefix, StringComparison.Ordinal)
            && hostOperations.TryGetByNativeName(fnName, out var hostOperation))
        {
            return await InvokeSynchronousHostOperationAsync(hostOperation, argNames, ctx, valEnv).ConfigureAwait(false);
        }

        var argsR = await CollectMathNativeArgumentsAsync(argNames, ctx, valEnv).ConfigureAwait(false);
        if (argsR.IsError) return argsR.Error;

        return ApplyMathNative(fnName, argsR.Value, ctx.Budget.RandomSource);
    }

    /// <summary>
    /// MIRROR OF <see cref="EvalCounted"/> — keep in lock-step, case for case.
    /// Cases whose synchronous counterpart delegated to the PLAIN evaluator award the
    /// counted twin's value projection instead; each such case notes the substitution.
    /// </summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalCountedAsync(
        Expr expr,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        // Bulk pathological-work bound — identical charging to the synchronous dispatch heads.
        if (ctx.Budget.TryChargeExpressionNodeWork() is { } nodeWorkError)
            return nodeWorkError;

        // MIRROR OF EvalCounted's compiler-exhaustive switch expression, case for case. A
        // new Expr variant is a build error here until it is given an explicit twin case
        // or joins the proven-leaf delegation group at the end — so a recursive variant
        // can never silently bypass the async twin family by evaluating its children
        // synchronously.
        // The Param and Resolve arms read `expr.Span` here rather than through the sync
        // twin's `EvalParamCountedOf` / `EvalResolveCountedOf` leaf frames: those exist for the
        // SYNCHRONOUS stack envelope (a span copy per dispatch frame), whereas this state
        // machine hoists its temporaries; the positioned outcome is identical either way.
        return expr switch
        {
            Expr.Param(var name) => await EvalParamCountedAsync(name, expr.Span, ctx, valEnv).ConfigureAwait(false),

            Expr.SequenceSpread => await EvalSequenceSpreadCountedAsync(expr, ctx, valEnv).ConfigureAwait(false),

            Expr.SequenceConstruct => await EvalSequenceConstructCountedAsync(expr, ctx, valEnv).ConfigureAwait(false),

            Expr.Unary or Expr.Binary or Expr.Comparison or Expr.ListLiteral => await EvalExpressionSpineCountedAsync(expr, ctx, valEnv).ConfigureAwait(false),

            Expr.EmptySequence(var depth) => CountValue(BuildEmptySequenceValue(depth)),

            Expr.AlgorithmExpr(var alg) => CountValue(await EvalAlgorithmExprValueAsync(expr, alg, ctx, valEnv).ConfigureAwait(false)),

            Expr.Capture(var captureBody) => CountValue(WithPreferredSpanOf(
                expr, captureBody,
                await EvalCaptureValueAsync(captureBody, ctx, valEnv).ConfigureAwait(false))),

            Expr.Resolve(var name) => await EvalResolveCountedAsync(name, expr.Span, ctx, valEnv).ConfigureAwait(false),

            Expr.DotCall dotCallExpr => WithSpanOf(expr, WithDotCallCtx(dotCallExpr, ctx,
                await EvalDotCallCountedAsync(dotCallExpr, ctx, valEnv).ConfigureAwait(false))),

            Expr.Call(var func, var callArgs) => WithSpanOf(expr,
                await EvalCallCountedExprAsync(func, callArgs, ctx, valEnv).ConfigureAwait(false)),

            Expr.Index => await EvalExpressionSpineCountedAsync(expr, ctx, valEnv).ConfigureAwait(false),

            // THE Phase 3 await site: an ASYNCHRONOUS host operation completes by
            // suspending the spine here. Every other native — a synchronous host
            // operation or a built-in Math member — takes the ordinary twin case
            // below, which awaits its declared-argument reads.
            Expr.NativeCall(var nativeFnName, var nativeArgNames)
                when ctx.Budget.HostOperations is { } hostOperations
                    && nativeFnName.StartsWith(HostOperations.NativeNamePrefix, StringComparison.Ordinal)
                    && hostOperations.TryGetByNativeName(nativeFnName, out var hostOperation)
                    && hostOperation.IsAsynchronous
                => await EvalAsynchronousHostOperationCountedAsync(
                    hostOperation, nativeArgNames, ctx, valEnv).ConfigureAwait(false),

            // A native wrapper's declared-argument reads ARE ordinary
            // Expr.Param value reads (LookupNativeArgument), so a demanded
            // algorithm-channel binding re-enters an algorithm body — that
            // makes NativeCall a recursive variant, not a leaf, and it must
            // stay on the twin family.
            Expr.NativeCall(var nativeFnName, var nativeArgNames)
                => CountValue(await EvalNativeCallAsync(nativeFnName, nativeArgNames, ctx, valEnv).ConfigureAwait(false)),

            // SYNC-DELEGABLE LEAVES — the only kinds allowed to run through
            // the synchronous evaluator on the twin path: none evaluates a
            // child expression, so delegating to the synchronous leaf core here
            // is exact — the same leaf code the synchronous counted dispatch
            // runs. The core is UNCHARGED (EvalLeafUncharged): this head already
            // charged the node's one bulk-work checkpoint, and entering the
            // plain Eval head instead charged a second one, so a leaf the
            // synchronous spine delivers through plain Eval cost one checkpoint
            // there and two here — the two strategies' step verdicts diverged at
            // scale. Grace is the illegal-in-eval catch-all (a structured
            // error, no child evaluation). Keep this classification in
            // lock-step with EvalCounted.
            Expr.Num or Expr.StringLiteral or Expr.BoolLiteral or Expr.Grace => CountValue(EvalLeafUncharged(expr, ctx)),
        };
    }

    /// <summary>
    /// MIRROR OF <see cref="EvalAlgorithmExprValue"/> — keep in lock-step. The sync
    /// helper calls the plain <c>EvalAlgOutput</c>; the twin awaits the counted core and
    /// projects its value (the plain wrapper is that projection).
    /// </summary>
    private static async ValueTask<EvalResult<Result>> EvalAlgorithmExprValueAsync(
        Expr expr,
        Algorithm alg,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        if (alg is Algorithm.Alias)
            return await EvalInlineAliasValueAsync(expr, alg, ctx, valEnv).ConfigureAwait(false);

        var wired = WireToCaller(ctx, alg);
        var blockSpan = PreferExpressionSpan(expr.Span, wired.Output);
        if (ZeroArgumentValueDemandRejection(ZeroArgumentDemandShape.Block, name: null, blockSpan, wired) is { } rejection)
            return rejection;
        return WithSpan(blockSpan, await EvalZeroArgumentDemandOutputAsync(wired, ctx, valEnv).ConfigureAwait(false));
    }

    /// <summary>
    /// MIRROR OF <see cref="EvalResolveCounted"/> — keep in lock-step: the zero-argument
    /// property access is awaited on the async cache seam.
    /// </summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalResolveCountedAsync(
        string name,
        SourceSpan? span,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        if (ctx.CallStack.Count == 0)
            return new EvalError.UnknownName(name) { Span = span };

        var resolvedR = LookupLexical(ctx.CallStack[0], name, ctx);
        if (resolvedR.IsError)
            return AtSpanIfMissing(resolvedR.Error, span);

        if (ZeroArgumentValueDemandRejection(ZeroArgumentDemandShape.Property, name, span, resolvedR.Value.ResolvedAlgorithm) is { } rejection)
            return rejection;

        var propertyR = WithPropertyContextOnMissingOutput(name, span, resolvedR.Value.ResolvedAlgorithm,
            await EvalZeroArgPropertyAccessCountedAsync(resolvedR.Value, ctx, valEnv).ConfigureAwait(false));
        return propertyR.IsError
            ? propertyR.Error
            : CountValue(propertyR.Value.Value);
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
        ValEnv valEnv)
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

                case Expr.Comparison(var first, var links):
                    {
                        if (frames[top].Phase == 0)
                        {
                            if (!hasPendingChild)
                            {
                                requestedChild = first;
                                break;
                            }

                            hasPendingChild = false;
                            frames[top].FirstValue = pendingChild.Value;
                            frames[top].Phase = 1;
                            if (links.Count == 0)
                            {
                                completed = EvalResult<CountedResult>.Ok(new CountedResult(new Result.Bool(true), 1));
                                break;
                            }

                            requestedChild = links[0].Operand;
                            break;
                        }

                        hasPendingChild = false;
                        var link = links[frames[top].Phase - 1];
                        var previousOperand = frames[top].Phase == 1 ? first : links[frames[top].Phase - 2].Operand;
                        var linkR = ApplyComparison(
                            link.Op, previousOperand, link.Operand, frames[top].FirstValue!, pendingChild.Value, frames[top].Node.Span);
                        if (linkR.IsError)
                        {
                            completed = linkR.Error;
                            break;
                        }

                        if (!linkR.Value)
                            frames[top].ComparisonFailed = true;
                        frames[top].FirstValue = pendingChild.Value;
                        frames[top].Phase++;
                        if (frames[top].Phase <= links.Count)
                        {
                            requestedChild = links[frames[top].Phase - 1].Operand;
                            break;
                        }

                        completed = EvalResult<CountedResult>.Ok(new CountedResult(new Result.Bool(!frames[top].ComparisonFailed), 1));
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

                        // MIRROR of the sync Index case: selection is a value
                        // boundary — the stored element, re-counted as one plain
                        // value (Result.ValueCount), never opened.
                        var selected = frames[top].FirstValue!.Index((int)n);
                        completed = selected is null
                            ? new EvalError.BadIndex() { Span = frames[top].Node.Span }
                            : CountValue(selected);
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
        ValEnv valEnv)
    {
        if (alg.DeferredRegion is { } region)
        {
            var materialized = await region.MaterializeAsync(ctx.Budget.CancellationToken).ConfigureAwait(false);
            if (materialized.IsError)
                return materialized.Error;
            // The materialized body takes the placeholder's parameter patterns and parent: Lean's
            // total withParameterPatterns and withParent, both narrowing to the owning variant.
            alg = WithParent(materialized.Value.WithParameterPatterns(alg.ParameterPatterns), alg.Parent);
        }

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

        return await EvalOutputRowsPreparedCoreAsync(alg.Output, EnterAlgorithmBody(alg, ctx, valEnv), ctx, valEnv).ConfigureAwait(false);
    }

    /// <summary>
    /// MIRROR OF <see cref="EvalOutputRowsPreparedCore"/> — keep in lock-step, INCLUDING
    /// the STRUCTURAL-NESTING STACK BACKSTOP at the head, which both families carry
    /// (rationale on the synchronous funnel: static nesting multiplied by dynamic
    /// recursion descends uncharged between two chokepoint probes). The twin needed it
    /// first because its async state-machine frames are larger than the calibrated
    /// synchronous frames, so this probe may stop a chain EARLIER than the synchronous
    /// one does on the same program; like the invocation-chokepoint probe it can only
    /// stop evaluation earlier than a physical overflow with the established structured
    /// error, never change a run that has host stack headroom, and it moves no budget
    /// counter.
    /// </summary>
    private static async ValueTask<EvalResult<PreparedAlgorithmOutput>> EvalOutputRowsPreparedCoreAsync(
        IReadOnlyList<Expr> rows,
        EvalCtx rowCtx,
        EvalCtx reserveCtx,
        ValEnv valEnv)
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

        if (ReserveSequenceCaptureAtRows(reserveCtx, results.Count, rows) is { } capturedLimitError)
            return capturedLimitError;

        var counted = new CountedResult(CombineOutputSlots(results), emittedCount);
        return EvalResult<PreparedAlgorithmOutput>.Ok(new(counted, results));
    }

    /// <summary>MIRROR OF <see cref="EvalCapturePreparedCore"/> — keep in lock-step.</summary>
    private static ValueTask<EvalResult<PreparedAlgorithmOutput>> EvalCapturePreparedCoreAsync(
        OutputBundle body,
        EvalCtx ctx,
        ValEnv valEnv)
        => EvalOutputRowsPreparedCoreAsync(body, ctx, ctx, valEnv);

    /// <summary>MIRROR OF <see cref="EvalCaptureCountedCore"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalCaptureCountedCoreAsync(
        OutputBundle body,
        EvalCtx ctx,
        ValEnv valEnv)
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
        ValEnv valEnv)
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
        ValEnv valEnv)
    {
        var preparedR = await EvalAlgOutputPreparedCoreAsync(alg, ctx, valEnv).ConfigureAwait(false);
        return preparedR.IsError
            ? preparedR.Error
            : EvalResult<CountedResult>.Ok(preparedR.Value.Counted);
    }

    /// <summary>
    /// MIRROR OF <see cref="EvalAlgOutputCore"/> / <see cref="EvalAlgOutputCore"/> — keep in
    /// lock-step. The synchronous wrapper projects <see cref="EvalAlgOutputCountedCore"/>;
    /// this async twin projects the identical counted field from the shared prepared core
    /// directly, avoiding a redundant async wrapper without owning any semantics.
    /// </summary>
    private static async ValueTask<EvalResult<Result>> EvalAlgOutputValueAsync(
        Algorithm alg,
        EvalCtx ctx,
        ValEnv valEnv)
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
        ValEnv valEnv,
        IReadOnlyList<string>? parameterNames = null)
    {
        if (alg is Algorithm.Builtin(var builtin))
        {
            var countedR = EvalBuiltinValueCounted(builtin);
            return countedR.IsError
                ? countedR.Error
                : EvalResult<IReadOnlyList<Result>>.Ok([countedR.Value.Value]);
        }

        if (alg.FindDuplicatePropName() is { } duplicateName)
            return new EvalError.DuplicateProperty(duplicateName);

        if (ConditionalValueAccessError("conditional", alg) is { } conditionalError)
            return conditionalError;

        if (alg is Algorithm.User { Output.Count: 0 })
            return new EvalError.MissingOutput();

        var slots = new List<Result>();
        var pushedCtx = EnterAlgorithmBody(alg, ctx, valEnv, parameterNames);
        foreach (var expr in alg.Output)
        {
            var countedR = await EvalCountedAsync(expr, pushedCtx, valEnv).ConfigureAwait(false);
            if (countedR.IsError) return countedR.Error;

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
        ValEnv valEnv)
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

        return await EvalExplicitSequenceValueRowSlotsAsync(alg.Output, EnterAlgorithmBody(alg, ctx, valEnv), valEnv).ConfigureAwait(false);
    }

    /// <summary>
    /// MIRROR OF <see cref="EvalExplicitSequenceValueRowSlots"/> — keep in lock-step,
    /// INCLUDING the structural-nesting stack backstop both families carry (see
    /// <see cref="EvalOutputRowsPreparedCoreAsync"/>): nested written groups recurse
    /// through this family without touching the ordinary dispatch or any invocation
    /// chokepoint.
    /// </summary>
    private static async ValueTask<EvalResult<IReadOnlyList<Result>>> EvalExplicitSequenceValueRowSlotsAsync(
        IReadOnlyList<Expr> rows,
        EvalCtx rowCtx,
        ValEnv valEnv)
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
        ValEnv valEnv)
    {
        // MIRROR: both unfolding arms position their failure at the written slot.
        if (expr is Expr.Capture(var captureBody))
        {
            var nestedItemsR = WithPreferredSpanOf(
                expr,
                captureBody,
                await EvalExplicitSequenceValueRowSlotsAsync(captureBody, ctx, valEnv).ConfigureAwait(false));
            if (nestedItemsR.IsError) return nestedItemsR.Error;

            return EvalResult<IReadOnlyList<Result>>.Ok([CombineOutputSlots(nestedItemsR.Value)]);
        }

        if (expr is Expr.AlgorithmExpr(var algorithm))
        {
            var wired = WireToCaller(ctx, algorithm);
            // MIRROR: only the plain-output arm may bypass zero-supply binding/dispatch.
            if (!RequiresZeroArgumentSupplyBinding(wired))
            {
                var nestedItemsR = WithPreferredSpanOf(
                    expr,
                    wired.Output,
                    await EvalExplicitSequenceValueItemsAsync(wired, ctx, valEnv).ConfigureAwait(false));
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

    // ── Zero-argument demand twins ─────────────────────────────────────────

    /// <summary>
    /// MIRROR OF <see cref="EvalZeroArgumentDemandOutputCounted"/> — keep in lock-step,
    /// including the split: the common no-pattern arm delegates straight to the core the
    /// demand sites awaited before (no extra state machine), and only a collecting-only
    /// or clause signature enters the binding arm.
    /// </summary>
    private static ValueTask<EvalResult<CountedResult>> EvalZeroArgumentDemandOutputCountedAsync(
        Algorithm algorithm,
        EvalCtx ctx,
        ValEnv valEnv)
        => RequiresZeroArgumentSupplyBinding(algorithm)
            ? EvalBoundZeroArgumentDemandOutputCountedAsync(algorithm, ctx, valEnv)
            : EvalAlgOutputCountedCoreAsync(algorithm, ctx, valEnv);

    /// <summary>MIRROR OF <see cref="EvalZeroArgumentDemandOutput"/> — keep in lock-step.</summary>
    private static ValueTask<EvalResult<Result>> EvalZeroArgumentDemandOutputAsync(
        Algorithm algorithm,
        EvalCtx ctx,
        ValEnv valEnv)
        => RequiresZeroArgumentSupplyBinding(algorithm)
            ? ProjectBoundZeroArgumentDemandValueAsync(algorithm, ctx, valEnv)
            : EvalAlgOutputValueAsync(algorithm, ctx, valEnv);

    /// <summary>MIRROR OF <see cref="EvalBoundZeroArgumentDemandOutputCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalBoundZeroArgumentDemandOutputCountedAsync(
        Algorithm algorithm,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        if (algorithm is Algorithm.Alias)
            return await EvalAliasZeroArgumentDemandCountedAsync(algorithm, ctx, valEnv).ConfigureAwait(false);

        if (algorithm is Algorithm.Conditional)
        {
            return await EvalConditionalCallCountedAsync(
                algorithm,
                OutputBundle.Empty,
                ctx,
                valEnv,
                CallDiagnosticName.FromKnown("conditional")).ConfigureAwait(false);
        }

        // Binding the EMPTY supply cannot suspend — there are no arguments to evaluate —
        // so the twins share the one synchronous binder.
        var bindingsR = BindZeroArgumentSupply(algorithm, ctx);
        if (bindingsR.IsError) return bindingsR.Error;

        var boundCtx = WithNeedBindings(ctx, bindingsR.Value!, algorithm.Params);
        var boundValues = ShadowValEnv(valEnv, algorithm.Params);
        return await EvalAlgOutputCountedCoreAsync(algorithm, boundCtx, boundValues)
            .ConfigureAwait(false);
    }

    private static async ValueTask<EvalResult<Result>> ProjectBoundZeroArgumentDemandValueAsync(
        Algorithm algorithm,
        EvalCtx ctx,
        ValEnv valEnv)
        => ProjectCountedValue(
            await EvalBoundZeroArgumentDemandOutputCountedAsync(algorithm, ctx, valEnv).ConfigureAwait(false));

    // ── Zero-argument property twins (the async host seam) ──────────────────

    /// <summary>MIRROR OF <see cref="EvaluateZeroArgPropertyResult"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<ZeroArgPropertyResult>> EvaluateZeroArgPropertyResultAsync(
        Algorithm resolvedAlgorithm,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        var countedR = await EvalZeroArgumentDemandOutputCountedAsync(resolvedAlgorithm, ctx, valEnv).ConfigureAwait(false);
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
        ValEnv valEnv)
    {
        // Charged dynamic invocation boundary, entered BEFORE the cache is consulted —
        // the SAME enter helper and scoped release as the synchronous twin
        // (Evaluator.BudgetScopes.cs), disposed on every completion path including
        // exceptional unwind through a suspended seam await.
        if (TryEnterDynamicInvocation(ctx, binding.FirstDeclarationSpan, out var level) is { } limitError)
            return limitError;

        using (level)
        {
            return await GetOrEvaluateZeroArgPropertyResultCoreAsync(
                owner, binding, accessKind, resolvedAlgorithm, ctx, valEnv).ConfigureAwait(false);
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
        ValEnv valEnv)
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
                ctx.NeedEnv.Count == 0 ? ValueEnvironmentCacheIdentity(valEnv) : ctx.NeedEnv,
                ctx.AlgEnv,
                ctx.CountedParamEnv,
                // The budget is the run identity, exactly as on the synchronous seam.
                ctx.Budget)
            { DeclaringScope = resolvedAlgorithm.Parent },
            () => EvaluateZeroArgPropertyResultAsync(resolvedAlgorithm, ctx, valEnv)).ConfigureAwait(false);
    }

    /// <summary>MIRROR OF <see cref="EvalZeroArgPropertyAccessCounted(Algorithm?, Property, ZeroArgPropertyAccessKind, Algorithm, EvalCtx, IReadOnlyList{ValueTuple{string, Result}})"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalZeroArgPropertyAccessCountedAsync(
        Algorithm? owner,
        Property binding,
        ZeroArgPropertyAccessKind accessKind,
        Algorithm resolvedAlgorithm,
        EvalCtx ctx,
        ValEnv valEnv)
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
        ValEnv valEnv)
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
        ValEnv valEnv)
    {
        if (ValidateHostOperationNativeSignature(hostOperation, argNames) is { } signatureError)
            return signatureError;

        // The declared-argument reads are ordinary Expr.Param value reads and can
        // demand an algorithm-channel binding's value, so they take the twin.
        var argumentsR = await CollectHostOperationArgumentsAsync(argNames, ctx, valEnv).ConfigureAwait(false);
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
        ValEnv valEnv)
    {
        if (TryEnterArgumentEvaluationLevel(ctx, out var level) is { } limitError)
            return limitError;

        using (level)
        {
            return await EvalZeroArgumentDemandOutputAsync(algorithm, ctx, valEnv).ConfigureAwait(false);
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
        ValEnv valEnv)
    {
        ThrowIfAsyncStrategyPinningViolated(ctx);

        var diagnosticName = CallDiagnosticName.FromExpression(func);
        var calleeR = ResolveCallee(func, ctx);
        if (calleeR.IsError)
            return CalleeResolutionFailure(diagnosticName, ctx, calleeR.Error);

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
        ValEnv valEnv,
        CallDiagnosticName calleeName)
    {
        // MIRROR — call(alias) = call(target).
        if (callee is Algorithm.Alias)
            return await EvalAliasCallCountedAsync(callee, args, ctx, valEnv, calleeName).ConfigureAwait(false);

        if (callee is Algorithm.Builtin(var builtinId))
        {
            var argAlgsR = await ResolveNeedSupply(args, ctx, valEnv, asynchronous: true).ConfigureAwait(false);
            if (argAlgsR.IsError) return argAlgsR.Error;
            return await ApplyBuiltinCountedResolvedAsync(builtinId, argAlgsR.Value, ctx, valEnv).ConfigureAwait(false);
        }

        if (TryGetFlatBinderUserEquivalent(callee) is { } simpleCallee)
            return await EvalUserCallCountedAsync(
                simpleCallee,
                args,
                ctx,
                valEnv,
                calleeName).ConfigureAwait(false);

        if (callee is Algorithm.Conditional)
            return await EvalConditionalCallCountedAsync(callee, args, ctx, valEnv, calleeName).ConfigureAwait(false);

        return await EvalUserCallCountedAsync(
            callee,
            args,
            ctx,
            valEnv,
            calleeName).ConfigureAwait(false);
    }

    /// <summary>MIRROR OF <see cref="EvalUserCallCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalUserCallCountedAsync(
        Algorithm callee, OutputBundle args,
        EvalCtx ctx,
        ValEnv valEnv,
        CallDiagnosticName calleeName)
    {
        // Charged dynamic invocation boundary (see EvaluationBudget) — the SAME enter
        // helper and scoped release as the synchronous twin (Evaluator.BudgetScopes.cs).
        if (TryEnterDynamicInvocation(ctx, UserCallLimitSpan(args), out var level) is { } limitError)
            return limitError;

        using (level)
        {
            return await EvalUserCallCountedCoreAsync(callee, args, ctx, valEnv, calleeName).ConfigureAwait(false);
        }
    }

    /// <summary>MIRROR OF <see cref="EvalUserCallCountedCore"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalUserCallCountedCoreAsync(
        Algorithm callee, OutputBundle args,
        EvalCtx ctx,
        ValEnv valEnv,
        CallDiagnosticName calleeName)
    {
        if (callee is Algorithm.User { AssignmentDeconstructionTarget: { } target } helper
            && await TryProjectSharedDeconstructionTargetAsync(helper, target, args, ctx, valEnv, calleeName).ConfigureAwait(false) is { } projected)
            return projected.IsError ? projected.Error : EvalResult<CountedResult>.Ok(new(projected.Value, projected.Value.ValueCount()));
        return await EvalNeedUserBody(callee, args, ctx, valEnv, calleeName, asynchronous: true).ConfigureAwait(false);
    }

    /// <summary>MIRROR OF <see cref="TryProjectSharedDeconstructionTarget"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<Result>?> TryProjectSharedDeconstructionTargetAsync(
        Algorithm.User helper,
        AssignmentDeconstructionTarget target,
        OutputBundle args,
        EvalCtx ctx,
        ValEnv valEnv,
        CallDiagnosticName calleeName)
    {
        var execution = new DeconstructionBindingExecution(target.Group, DeconstructionOwnerIdentity(ctx),
            ctx.NeedEnv.Count == 0 ? ValueEnvironmentCacheIdentity(valEnv) : ctx.NeedEnv, ctx.AlgEnv, ctx.CountedParamEnv);
        var sharedR = await ctx.DeconstructionBindingCache.GetOrBindAsync(execution,
            () => BindNeedDeconstruction(helper, args, ctx, valEnv, asynchronous: true)).ConfigureAwait(false);
        if (sharedR.IsError) return sharedR.Error;
        if ((uint)target.Index >= (uint)sharedR.Value.Count) return null;
        return ProjectCountedValue(await sharedR.Value[target.Index].DemandAsync().ConfigureAwait(false));
    }

    /// <summary>MIRROR OF <see cref="EvalConditionalCallCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalConditionalCallCountedAsync(
        Algorithm callee, OutputBundle args,
        EvalCtx ctx,
        ValEnv valEnv,
        CallDiagnosticName calleeName)
    {
        // Charged dynamic invocation boundary; this counted core owns the
        // boundary for both counted evaluation and its plain projection.
        if (ctx.Budget.TryEnterInvocation() is { } limitError)
            return AtFirstSpanIfMissing(limitError, args);

        try
        {
            return await EvalConditionalCallCountedCoreAsync(callee, args, ctx, valEnv, calleeName).ConfigureAwait(false);
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
        ValEnv valEnv,
        CallDiagnosticName calleeName)
    {
        return await EvalNeedFamilyBody(callee, args, ctx, valEnv, calleeName, asynchronous: true).ConfigureAwait(false);
    }



    // ── Argument-assembly and binding twins ─────────────────────────────────

    /// <summary>MIRROR OF <see cref="RejectDotStringIntrinsicArguments"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalError?> RejectDotStringIntrinsicArgumentsAsync(
        OutputBundle? argsOpt,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        if (argsOpt is null)
            return null;

        var inputsR = await FormNeedSupply(argsOpt, ctx, valEnv, asynchronous: true).ConfigureAwait(false);
        if (inputsR.IsError)
            return inputsR.Error;

        return inputsR.Value.Count == 0 ? null : new EvalError.ArityMismatch(0, inputsR.Value.Count);
    }









    // ── Builtin twins ───────────────────────────────────────────────────────

    /// <summary>MIRROR OF <see cref="ApplyBuiltinCountedResolved"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> ApplyBuiltinCountedResolvedAsync(
        BuiltinId builtin,
        IReadOnlyList<ResolvedArgumentAlgorithm> resolvedArgs,
        EvalCtx ctx,
        ValEnv valEnv)
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
                    var truth = condR.Value.AsBool();
                    if (truth is null)
                        return new EvalError.TypeMismatch(BooleanRequiredMessage("if condition", condR.Value));

                    // The selected branch is one value boundary — see the synchronous twin.
                    var branchR = truth.Value
                        ? await EvalResolvedArgumentCountedAsync(args[1], ctx, valEnv).ConfigureAwait(false)
                        : await EvalResolvedArgumentCountedAsync(args[2], ctx, valEnv).ConfigureAwait(false);
                    if (branchR.IsError) return branchR.Error;
                    return EvalResult<CountedResult>.Ok(
                        new CountedResult(branchR.Value.Value, branchR.Value.Value.ValueCount()));
                }

            case (BuiltinId.@while, _) when args.Count >= 2:
            case (BuiltinId.@repeat, _) when args.Count >= 3:
                return await EvalNeedLoop(builtin, args, ctx, valEnv, asynchronous: true).ConfigureAwait(false);

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
    /// <see cref="ValidateRangeBound"/>, so the range bound policy (whole integer,
    /// magnitude within the exact-unit-step domain, canonical integer representation)
    /// cannot drift between the sync and async paths.
    /// </summary>
    private static async ValueTask<EvalResult<InclusiveRange>> EvalBuiltinRangeArgumentsAsync(
        IReadOnlyList<ResolvedArgumentAlgorithm> args,
        EvalCtx ctx,
        ValEnv valEnv)
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

    /// <summary>MIRROR OF <see cref="EvalResolvedArgumentCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalResolvedArgumentCountedAsync(
        ResolvedArgumentAlgorithm arg,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        if (arg.Cell is { } cell)
        {
            var result = await cell.DemandAsync().ConfigureAwait(false);
            return arg.Source is Expr.Param(var name) ? DemandParameter(cell, result, name, arg.Source.Span) : result;
        }
        if (arg.PreparedValue is { } prepared)
            return EvalResult<CountedResult>.Ok(prepared);
        if (ParameterValueFailure(arg.Source, ctx, valEnv) is { } slotFailure)
            return slotFailure;
        if (arg.Algorithm is not { } algorithm)
            return new EvalError.BadArity();

        // The ONE zero-argument value-demand law decides from the NAMED callable before
        // any body (or the argument level) is entered; the demand reads the value side —
        // see the synchronous twin.
        if (ZeroArgumentValueDemandError(arg.Source, arg.InvokedAlgorithm ?? algorithm) is { } rejection)
            return rejection;

        return BlameDemandedArgumentForMissingOutput(
            arg.Source,
            await EvalArgumentAlgOutputCountedAsync(algorithm, ctx, valEnv).ConfigureAwait(false));
    }

    /// <summary>MIRROR OF <see cref="EvalResolvedArgument"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<Result>> EvalResolvedArgumentValueAsync(
        ResolvedArgumentAlgorithm arg,
        EvalCtx ctx,
        ValEnv valEnv)
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
        ValEnv valEnv)
    {
        // The SAME enter helper and scoped release as the synchronous twin
        // (Evaluator.BudgetScopes.cs).
        if (TryEnterArgumentEvaluationLevel(ctx, out var level) is { } limitError)
            return limitError;

        using (level)
        {
            return await EvalZeroArgumentDemandOutputCountedAsync(algorithm, ctx, valEnv).ConfigureAwait(false);
        }
    }

    /// <summary>MIRROR OF <see cref="ExpandSequenceSpreadBuiltinArguments"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<IReadOnlyList<ResolvedArgumentAlgorithm>>> ExpandSequenceSpreadBuiltinArgumentsAsync(
        IReadOnlyList<ResolvedArgumentAlgorithm> args,
        EvalCtx ctx,
        ValEnv valEnv)
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
        ValEnv valEnv,
        SequenceBuiltinMetadata metadata)
    {
        var expanded = await ExpandSequenceSpreadBuiltinArgumentsAsync(args, ctx, valEnv).ConfigureAwait(false);
        return expanded.IsError ? expanded.Error : EvalResult<IReadOnlyList<VariadicCallItem>>.Ok(expanded.Value.Select(UnevaluatedCallItem).ToArray());
    }

    /// <summary>MIRROR OF <see cref="DemandSequenceBuiltinCallItemValue"/> — keep in lock-step.</summary>
    private static async ValueTask<VariadicCallItem> DemandSequenceBuiltinCallItemValueAsync(
        VariadicCallItem item,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        if (item.Cell is { } cell && item.Value is null && item.ValueError is null)
        {
            var result = await cell.DemandAsync().ConfigureAwait(false);
            return FinishNeedCallItemDemand(item, cell, result);
        }
        if (item.Value is null && item.ValueError is null
            && ParameterValueFailure(item.Source, ctx, valEnv) is { } slotFailure)
            return item with { ValueError = slotFailure };

        if (item.Value is not null
            || item.ValueError is not null
            || item.Algorithm is not { } algorithm
            || !AcceptsZeroArgumentValueDemand(item.Callable ?? algorithm))
        {
            return item;
        }

        var demandedR = await EvalArgumentAlgOutputCountedAsync(algorithm, ctx, valEnv).ConfigureAwait(false);
        return demandedR.IsError
            ? item with { ValueError = BlameDemandedArgumentForMissingOutput(item.Source, demandedR).Error }
            : item with { Value = demandedR.Value.Value, PreparedValue = demandedR.Value };
    }

    /// <summary>MIRROR OF <see cref="BindSequenceBuiltinArguments"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<BoundSequenceBuiltinArguments>> BindSequenceBuiltinArgumentsAsync(
        BuiltinId builtin,
        SequenceBuiltinMetadata metadata,
        IReadOnlyList<ResolvedArgumentAlgorithm> args,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        var descriptor = BuiltinRegistry.GetBuiltin(builtin);
        var signature = descriptor.PlainSignature;
        var itemsR = await BuildCallableCallItemsAsync(args, ctx, valEnv, metadata).ConfigureAwait(false);
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

        // The `collection` parameter is a VALUE position — see the synchronous twin.
        var collectionItem = await DemandSequenceBuiltinCallItemValueAsync(items[0], ctx, valEnv).ConfigureAwait(false);
        if (collectionItem.Value is null)
            return SequenceBuiltinValueDemandError(collectionItem) ?? new EvalError.BadArity();

        var collectionValues = BuiltinCollectionItems(collectionItem.Value);

        var collected = new CollectedSequenceBuiltinInput(collectionValues);
        var preparedInputR = PrepareSequenceBuiltinInput(builtin, metadata, collected);
        if (preparedInputR.IsError) return preparedInputR.Error;

        var suffixArgs = new List<PreparedSequenceBuiltinSuffixArg>(metadata.SuffixArgs.Count);
        for (var index = 0; index < metadata.SuffixArgs.Count; index++)
        {
            // A Value / WholeNumber control is a VALUE position, so it is demanded here —
            // asynchronously, before the shared synchronous preparation reads it (the
            // preparer's own demand then finds the item already resolved). An Algorithm
            // control is a CALLBACK slot and is never demanded.
            var controlItem = items[1 + index];
            if (metadata.SuffixArgs[index].Kind != SequenceBuiltinSuffixArgKind.Algorithm)
                controlItem = await DemandSequenceBuiltinCallItemValueAsync(controlItem, ctx, valEnv).ConfigureAwait(false);

            var preparedArgR = PrepareSequenceBuiltinSuffixArg(
                builtin,
                metadata.SuffixArgs[index],
                controlItem,
                ctx,
                valEnv);
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
        ValEnv valEnv)
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
                    if (bound.IterationItems.Count == 0) return MakeCollectionListResult(ctx, []);
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
                    if (bound.IterationItems.Count == 0) return MakeCollectionListResult(ctx, []);
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
                    var initialR = ExpectPreparedValueSuffixArg(
                        builtin,
                        metadata.SuffixArgs,
                        bound.SuffixArgs,
                        1);
                    if (initialR.IsError) return initialR.Error;
                    if (bound.IterationItems.Count == 0) return EvalResult<CountedResult>.Ok(new(initialR.Value, initialR.Value.ValueCount()));

                    var stepR = ExpectPreparedAlgorithmSuffixArg(
                        builtin,
                        metadata.SuffixArgs,
                        bound.SuffixArgs,
                        0);
                    if (stepR.IsError) return stepR.Error;

                    return await EvalReduceCountedAsync(
                        bound.IterationItems,
                        stepR.Value,
                        initialR.Value,
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
        ValEnv valEnv,
        string calleeName = "conditional")
    {
        // MIRROR — a callback that is an alias is its target, before the invocation charge.
        if (callee is Algorithm.Alias)
            return await EvalAliasCallbackCallCountedAsync(callee, args, ctx, valEnv, calleeName).ConfigureAwait(false);

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
        ValEnv valEnv,
        string calleeName)
    {
        return await EvalNeedCallbackBody(callee, args, ctx, valEnv, calleeName, asynchronous: true).ConfigureAwait(false);
    }

    /// <summary>MIRROR OF <see cref="EvalSequenceCallbackCallCounted"/> — keep in lock-step.</summary>
    private static ValueTask<EvalResult<CountedResult>> EvalSequenceCallbackCallCountedAsync(
        Algorithm callee,
        CountedResult item,
        EvalCtx ctx,
        ValEnv valEnv,
        string calleeName = "conditional")
        => EvalResolvedCallbackCallCountedAsync(callee, [CountedSequenceCallbackItem(item)], ctx, valEnv, calleeName);

    /// <summary>MIRROR OF <see cref="EvalSequenceReduceStepCounted"/> — keep in lock-step.</summary>
    private static ValueTask<EvalResult<CountedResult>> EvalSequenceReduceStepCountedAsync(
        Algorithm callee,
        CountedResult element,
        Result accumulator,
        EvalCtx ctx,
        ValEnv valEnv,
        string calleeName = "conditional")
        => EvalResolvedCallbackCallCountedAsync(
            callee,
            [CountedSequenceCallbackItem(element), new CountedResult(accumulator, accumulator.ValueCount())],
            ctx,
            valEnv,
            calleeName);

    // ── map/filter/reduce twins ─────────────────────────────────────────────

    /// <summary>MIRROR OF <see cref="EvalReduceCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalReduceCountedAsync(
        IReadOnlyList<CountedResult> items,
        Algorithm stepAlg,
        Result initial,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        // The initial accumulator is an ordinary VALUE slot that binding already demanded
        // once; it occupies ONE written accumulator slot — see the synchronous twin.
        var accumulator = new CountedResult(initial, initial.ValueCount());
        foreach (var item in items)
        {
            var stepR = WithCtx(
                "while evaluating reduce step (reduce passes each iterated collection item as collected and the accumulator as one value; a collecting parameter collects supplied values as one exact list and nested sequence and list values stay intact)",
                await EvalSequenceReduceStepCountedAsync(stepAlg, item, accumulator.Value, ctx, valEnv, ReduceStepFrameName).ConfigureAwait(false));
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
        ValEnv valEnv)
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
        ValEnv valEnv)
    {
        var predicateCountedR = await EvalSequenceCallbackCallCountedAsync(
            predicateAlg, item, ctx, valEnv, FilterPredicateFrameName).ConfigureAwait(false);
        var predicateR = WithFilterItemCtx(
            item.Value,
            index,
            ctx,
            predicateCountedR.IsError
                ? EvalResult<Result>.Err(predicateCountedR.Error)
                : EvalResult<Result>.Ok(predicateCountedR.Value.Value));
        if (predicateR.IsError)
            return predicateR.Error;

        // MIRROR of EvalFilterPredicateTruth: the predicate must return a Boolean value.
        var truth = predicateR.Value.AsBool();
        if (truth is null)
            return new EvalError.TypeMismatch(BooleanRequiredMessage("filter predicate result", predicateR.Value));

        return EvalResult<bool>.Ok(truth.Value);
    }

    /// <summary>MIRROR OF <see cref="EvalMapCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalMapCountedAsync(
        IReadOnlyList<CountedResult> items,
        Algorithm transformAlg,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        var mapped = new List<Result>(items.Count);
        foreach (var item in items)
        {
            var transformR = WithCtx(
                "while evaluating map transform (map passes each iterated collection item as collected; a collecting parameter collects supplied values as one exact list and nested sequence and list values stay intact)",
                await EvalSequenceCallbackCallCountedAsync(transformAlg, item, ctx, valEnv, MapTransformFrameName).ConfigureAwait(false));
            if (transformR.IsError) return transformR.Error;

            var mappedElementR = ExpectSingleMappedElement(transformR.Value);
            if (mappedElementR.IsError) return mappedElementR.Error;

            mapped.Add(mappedElementR.Value);
        }

        return MakeCollectionListResult(ctx, mapped);
    }

    // ── Loop twins ──────────────────────────────────────────────────────────

    /// <summary>
    /// MIRROR OF <see cref="EvalDotCallCounted"/> — keep in lock-step. The sequence
    /// pipeline attempt is omitted under the async strategy pinning (see
    /// <see cref="ThrowIfAsyncStrategyPinningViolated"/>).
    /// </summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalDotCallCountedAsync(
        Expr.DotCall dotCall,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        ThrowIfAsyncStrategyPinningViolated(ctx);

        var target = dotCall.Target;
        var name = dotCall.Name;
        var argsOpt = dotCall.Args;

        var targetResult = ResolveDotReceiver(target, ctx, out var receiverIsStructuralMember);
        if (targetResult.IsError)
        {
            if (targetResult.Error is EvalError.NotAnAlgorithm)
            {
                // MIRROR — a value receiver declares no member: the miss route applies directly.
                if (dotCall.UsesOrdinaryDotStringIntrinsic())
                {
                    if (await RejectDotStringIntrinsicArgumentsAsync(argsOpt, ctx, valEnv).ConfigureAwait(false) is { } arityRejection)
                        return arityRejection;
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

        // MIRROR — ONE structural lookup decides the route; a member named `string` wins too.
        var prop = LookupPropBinding(targetAlg, name, ctx.Budget);
        if (prop is not null)
        {
            if (!IsAccessibleFrom(prop, targetAlg, ctx))
                return LocalOnlyPropertyError(OpenExprName(target), prop);

            var wired = ChildOfInContext(targetAlg, prop.Value, ctx);
            // MIRROR — a member that is an alias is read and called as its target.
            if (wired is Algorithm.Alias)
                return await EvalAliasMemberCountedAsync(targetAlg, prop, wired, argsOpt, name, ctx, valEnv).ConfigureAwait(false);
            if (argsOpt is null)
            {
                // See the synchronous twin: the ONE law decides, and the rejection names
                // the member's true minimum supply.
                var simpleCallee = TryGetFlatBinderUserEquivalent(wired);
                if (simpleCallee is not null)
                {
                    return AcceptsZeroArgumentValueDemand(simpleCallee)
                        ? MarkSelectedMemberOutput(ReCountValueBoundary(
                            await EvalZeroArgPropertyAccessCountedAsync(
                                targetAlg, prop, ZeroArgPropertyAccessKind.CountedStructural, simpleCallee, ctx, valEnv).ConfigureAwait(false)))
                        : ZeroArgumentDemandArityMismatch(simpleCallee);
                }

                if (AcceptsZeroArgumentValueDemand(wired))
                    return MarkSelectedMemberOutput(ReCountValueBoundary(
                        await EvalZeroArgPropertyAccessCountedAsync(
                            targetAlg, prop, ZeroArgPropertyAccessKind.CountedStructural, wired, ctx, valEnv).ConfigureAwait(false)));

                if (wired is Algorithm.Conditional)
                    return new EvalError.NoMatchingBranch(name);

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

        // MIRROR — a structural miss: `string` is the intrinsic, every other member the extension call.
        if (dotCall.UsesOrdinaryDotStringIntrinsic())
        {
            if (await RejectDotStringIntrinsicArgumentsAsync(argsOpt, ctx, valEnv).ConfigureAwait(false) is { } arityRejection)
                return arityRejection;
            // MIRROR — the `.string` receiver is judged on the alias's target.
            if (targetAlg is Algorithm.Alias)
                return await EvalAliasDotStringCountedAsync(target, targetAlg, receiverIsStructuralMember, ctx, valEnv).ConfigureAwait(false);
            var val = await EvalDotStringReceiverAlgOutputAsync(target, targetAlg, receiverIsStructuralMember, ctx, valEnv).ConfigureAwait(false);
            if (val.IsError) return val.Error;
            var outR = ResultToString(ctx, val.Value);
            if (outR.IsError) return outR.Error;
            return EvalResult<CountedResult>.Ok(new CountedResult(outR.Value, outR.Value.ValueCount()));
        }

        return await CallLexicalWithReceiverCountedAsync(dotCall, ctx, valEnv).ConfigureAwait(false);
    }

    /// <summary>MIRROR OF <see cref="CallLexicalWithReceiverCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> CallLexicalWithReceiverCountedAsync(
        Expr.DotCall dotCall,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        // Stored-fallback consumption — see CallLexicalWithReceiverCounted. DOT-CALL
        // PASSES A VALUE: the receiver is the ordinary first argument of `F(R, args)`.
        if (dotCall.EffectiveLexicalFallback is not Expr.Resolve(var fallbackName))
            return await CallLexicalFallbackCalleeWithReceiverCountedAsync(dotCall, ctx, valEnv).ConfigureAwait(false);

        var calleeR = ResolveNamedAlgorithm(fallbackName, span: null, ctx);
        if (calleeR.IsError) return calleeR.Error;
        return await EvalResolvedCallCountedAsync(
            calleeR.Value,
            BuildLexicalReceiverCallArgs(dotCall.Target, dotCall.Args),
            ctx,
            valEnv,
            CallDiagnosticName.FromKnown(fallbackName)).ConfigureAwait(false);
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
        ValEnv valEnv)
    {
        var calleeR = ResolveAlg(dotCall.EffectiveLexicalFallback, ctx);
        if (calleeR.IsError) return calleeR.Error;
        return await EvalResolvedCallCountedAsync(
            calleeR.Value,
            BuildLexicalReceiverCallArgs(dotCall.Target, dotCall.Args),
            ctx,
            valEnv,
            CallDiagnosticName.FromKnown(dotCall.Name)).ConfigureAwait(false);
    }

    /// <summary>MIRROR OF <see cref="EvalDotStringReceiverAlgOutput"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<Result>> EvalDotStringReceiverAlgOutputAsync(
        Expr target,
        Algorithm targetAlg,
        bool receiverIsStructuralMember,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        if (target is Expr.Param(var needName) && LookupNeed(ParameterContext(needName, ctx, ref valEnv).NeedEnv, needName) is not null)
            return ProjectCountedValue(await EvalParamCountedAsync(needName, target.Span, ctx, valEnv).ConfigureAwait(false));

        // A PARAMETER receiver whose argument slot FAILED its one value evaluation reports
        // that recorded failure first — see the synchronous twin.
        if (target is Expr.Param(var paramName)
            && ParameterValueFailure(paramName, ctx, valEnv) is { } slotFailure)
        {
            return ParameterSlotFailure(paramName, target.Span, slotFailure);
        }

        // The receiver is demanded for its VALUE with zero arguments — see the
        // synchronous twin.
        if (ZeroArgumentValueDemandError(target, targetAlg) is { } rejection)
            return rejection;

        // The accepted receiver is READ exactly as a value position reads it — see the
        // synchronous twin.
        switch (target)
        {
            case Expr.Param(var name):
                // MIRROR OF the synchronous twin: the ordinary value-position parameter read
                // (its bound value first; a missing output is the parameter's failure).
                return ProjectCountedValue(await EvalParamCountedAsync(name, target.Span, ctx, valEnv).ConfigureAwait(false));

            case Expr.Resolve(var name):
                return await EvalDotStringLexicalPropertyReceiverAsync(target, name, ctx, valEnv).ConfigureAwait(false);

            case Expr.DotCall edge when receiverIsStructuralMember:
                return await EvalDotStringStructuralMemberReceiverAsync(edge, targetAlg, ctx, valEnv).ConfigureAwait(false);

            default:
                return await EvalZeroArgumentDemandOutputAsync(targetAlg, ctx, valEnv).ConfigureAwait(false);
        }
    }

    /// <summary>MIRROR OF <see cref="EvalDotStringLexicalPropertyReceiver"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<Result>> EvalDotStringLexicalPropertyReceiverAsync(
        Expr target,
        string name,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        if (ctx.CallStack.Count == 0)
            return new EvalError.UnknownName(name) { Span = target.Span };

        var resolvedR = LookupLexical(ctx.CallStack[0], name, ctx);
        if (resolvedR.IsError)
            return AtSpanIfMissing(resolvedR.Error, target.Span);

        if (TryEnterArgumentEvaluationLevel(ctx, out var level) is { } limitError)
            return limitError;

        using (level)
        {
            return ProjectCountedValue(await EvalZeroArgPropertyAccessCountedAsync(resolvedR.Value, ctx, valEnv).ConfigureAwait(false));
        }
    }

    /// <summary>MIRROR OF <see cref="EvalDotStringStructuralMemberReceiver"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<Result>> EvalDotStringStructuralMemberReceiverAsync(
        Expr.DotCall edge,
        Algorithm targetAlg,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        var containerR = ResolveDotReceiver(edge.Target, ctx, out _);
        if (containerR.IsOk && LookupPropBinding(containerR.Value, edge.Name, ctx.Budget) is { } member)
        {
            if (TryEnterArgumentEvaluationLevel(ctx, out var level) is { } limitError)
                return limitError;

            using (level)
            {
                return ProjectCountedValue(await EvalZeroArgPropertyAccessCountedAsync(
                    containerR.Value,
                    member,
                    ZeroArgPropertyAccessKind.CountedStructural,
                    TryGetFlatBinderUserEquivalent(targetAlg) ?? targetAlg,
                    ctx,
                    valEnv).ConfigureAwait(false));
            }
        }

        return await EvalResolvedAlgOutputForValueDemandAsync(targetAlg, ctx, valEnv).ConfigureAwait(false);
    }

    // ── Sequence-join twins ─────────────────────────────────────────────────

    /// <summary>MIRROR OF <see cref="EvalSequenceConstructCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalSequenceConstructCountedAsync(
        Expr expr,
        EvalCtx ctx,
        ValEnv valEnv)
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
        ValEnv valEnv)
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
            if (alg is Algorithm.Alias)
                return await EvalAliasSpreadOperandItemsAsync(expr, alg, ctx, valEnv).ConfigureAwait(false);

            var wired = WireToCaller(ctx, alg);
            var blockSpan = PreferExpressionSpan(expr.Span, wired.Output);
            // See the synchronous twin: a spread operand is a zero-argument value demand.
            if (ZeroArgumentValueDemandRejection(ZeroArgumentDemandShape.Block, name: null, blockSpan, wired) is { } rejection)
                return rejection;

            var blockR = await EvalZeroArgumentDemandOutputAsync(wired, ctx, valEnv).ConfigureAwait(false);
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
        ValEnv valEnv)
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
