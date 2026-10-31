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
///   <see cref="IAsyncZeroArgPropertyResultCache"/>, no ASYNCHRONOUS
///   <see cref="HostOperation"/> is configured, and the tree carries no deferred module
///   region — every run without async host operations whose program has no clause branch
///   that loads its modules on demand), the async entry point executes the ORDINARY
///   synchronous pipeline inline on the calling thread and returns an already-completed
///   task. Behavior, budget accounting, optimizer strategy selection, stack shape, and
///   cancellation are those of the synchronous entry point, by identity — the same code
///   runs. There is no thread offloading and no artificial yielding.</item>
///   <item><b>Async twin path</b> — when a run component IS async-capable, evaluation
///   runs through the <c>*Async</c> twin methods in this file. Each twin MIRRORS its
///   synchronous counterpart's sequencing exactly (marked <c>// MIRROR OF ...</c>) and
///   must be kept in lock-step with it; the twins share every non-evaluating helper
///   (lookup, binding matchers, budget chokepoints, value construction, diagnostics)
///   with the synchronous family and re-implement only the child-evaluation sequencing
///   that must be awaitable. A genuinely asynchronous operation — the internal cache
///   seam, a public asynchronous <see cref="HostOperation"/> awaited at its wrapper-body
///   site, or the module download awaited when a selected deferred branch is materialized
///   — suspends the whole spine and resumes it on completion.</item>
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
    /// <para>For a tree without a deferred module region, an uncancelled run produces
    /// exactly the result, diagnostics, and limit verdict of the synchronous overload, and
    /// because this overload carries no asynchronous host component, the returned task
    /// completes synchronously on the calling thread: this method never schedules
    /// evaluation onto another thread and never yields artificially — host scheduling
    /// (thread placement, offloading) remains the host's responsibility. Genuinely
    /// asynchronous host operations are configured through
    /// <see cref="RunAsync(Expr, HostOperations, EvaluationLimits?, long?, CancellationToken)"/>
    /// (or <see cref="RunOptions.HostOperations"/> at the engine level), where an
    /// incomplete host awaitable suspends and resumes the run.</para>
    ///
    /// <para>A tree carrying a deferred module region — a clause branch whose modules load
    /// only when evaluation selects it, which <see cref="Parser.ParseAsync"/> produces when
    /// <see cref="RunOptions.DownloadCode"/> is configured — is the exception to both
    /// statements: the synchronous overload rejects it with
    /// <see cref="InvalidOperationException"/> before evaluating it, and this overload runs
    /// it on the async twin path, where materializing a selected branch can await the module
    /// downloader and genuinely suspend the run. Such a run has the twin path's host-stack
    /// behavior, described under <see cref="EvaluationLimits.MaxDepth"/>.</para>
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
        // SEC-F5: an already-cancelled token stops the run before the cache-pairing
        // factory and the route selection each scan the host-built tree.
        cancellationToken.ThrowIfCancellationRequested();
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
    /// <para>With only synchronous operations configured, and a tree that carries no
    /// deferred module region, the run keeps the synchronous fast path: the returned task
    /// completes synchronously on the calling thread, and behavior is that of the
    /// synchronous host-operation overload by identity. With at least one asynchronous
    /// operation, or a tree carrying a deferred module region (which the synchronous
    /// overload rejects; see <see cref="RunAsync(Expr, EvaluationLimits?, CancellationToken)"/>),
    /// the run executes through the async twin path. An incomplete
    /// <see cref="ValueTask{TResult}"/> returned by an operation genuinely suspends the
    /// evaluation — no thread is blocked, nothing is replayed — resuming at the same point
    /// when the operation completes. Each operation receives
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
        // SEC-F5: as above — after argument validation, before any tree work.
        cancellationToken.ThrowIfCancellationRequested();
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
    /// There are exactly three such components — an async-capable zero-argument property
    /// cache (the internal Phase 2 seam), a configured ASYNCHRONOUS host operation (the
    /// public Phase 3 surface, which awaits at its wrapper-body site), and a deferred
    /// module region anywhere in the tree (B2c: materializing a selected branch can await
    /// the module downloader; <see cref="DeferredModuleRegion.RequiresAsyncEvaluation"/>).
    /// Everything else — including a configuration of purely SYNCHRONOUS host operations,
    /// whose delegates complete inline by contract — takes the synchronous pipeline inline:
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
    /// evaluated eagerly, double-evaluating on hits). A run that selects the twin path
    /// through asynchronous host operations or a deferred module region must therefore
    /// also carry an async-capable cache; the public entry points construct one, and this
    /// guard makes the requirement fail-loud for internal callers instead of surfacing later
    /// as the twin family's mid-run ownership exception.
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
    /// result cache from its host-operation configuration and its tree: a configuration
    /// containing an ASYNCHRONOUS operation, or a tree carrying a deferred module region,
    /// routes the run through the async twin path, which awaits the property seam — so it
    /// is paired with the async-capable run-scoped cache; every other run (no host
    /// operations or purely synchronous ones, and no deferred module region) keeps the
    /// ordinary run-scoped cache and with it the synchronous fast path.
    /// Every call constructs a FRESH cache belonging to one run alone — the pairing
    /// rule never introduces sharing. An engine run's optional
    /// <paramref name="observationSink"/> is attached to whichever cache the rule selects and
    /// takes no part in the selection.
    /// <see cref="ThrowIfAsyncHostOperationsWithoutAsyncCapableCache"/> enforces the
    /// same pairing fail-loud for internal callers that supply their own cache.
    /// </summary>
    internal static IZeroArgPropertyResultCache CreateRunScopedZeroArgPropertyResultCache(
        Expr expr,
        HostOperations? hostOperations,
        RootPropertyObservationSink? observationSink = null)
        => hostOperations?.ContainsAsynchronousOperations == true
            // B2c: a root carrying deferred module regions runs on the twin path too, and
            // so pairs with the async-capable cache by the same rule.
            || DeferredModuleRegion.RequiresAsyncEvaluation(expr)
            ? new RunScopedAsyncZeroArgPropertyResultCache(observationSink)
            : new RunScopedZeroArgPropertyResultCache(observationSink);

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
            asynchronousRun: true,
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
        using var preparation = PrepareAsyncTwinRun(
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

        // The run result boundary and the completion-boundary observation, exactly as on the
        // synchronous path.
        result = ExportRunValue(result, ctx);
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
        using var preparation = PrepareAsyncTwinRun(
            expr, zeroArgPropertyResultCache, loopDiagnostics: null, sequenceDiagnostics: null, limits, observations: null, hostOperations, randomSeed, cancellationToken);
        if (preparation.Error is { } preparationError)
            return preparationError;

        var ctx = preparation.Ctx;
        var result = ExportRunValue(expr is Expr.AlgorithmExpr(var alg)
            ? await EvalRootProgramCountedAsync(alg, expr.Span, ctx).ConfigureAwait(false)
            : await EvalCountedAsync(expr, ctx, []).ConfigureAwait(false), ctx);

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
        using var preparation = PrepareAsyncTwinRun(
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

        result = ExportRunValue(result, ctx);
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
        using var preparation = PrepareAsyncTwinRun(
            expr, cache, loopDiagnostics, sequenceDiagnostics, limits, observations, hostOperations, randomSeed, cancellationToken);
        if (preparation.Error is { } preparationError)
            return (preparationError, preparation.Budget);

        var ctx = preparation.Ctx;
        var result = ExportRunValue(expr is Expr.AlgorithmExpr(var alg)
            ? await EvalRootProgramCountedAsync(alg, expr.Span, ctx).ConfigureAwait(false)
            : await EvalCountedAsync(expr, ctx, []).ConfigureAwait(false), ctx);

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

        // An alias binding reads its VALUE terminal (OD-E, M4★): the terminal binding's own entry, or a
        // runtime-target alias's binding cell — never an entry of its own.
        var resolvedR = await NormalizeTopLevelBindingAsync(alg, binding, ChildOf(alg, binding.Value), ctx).ConfigureAwait(false);
        if (resolvedR.IsError)
            return resolvedR.Error;
        var resolvedAlgorithm = resolvedR.Value.ResolvedAlgorithm;
        var span = binding.FirstDeclarationSpan;
        // A named top-level property read is an ordinary zero-argument value demand, so
        // the ONE law decides and shapes its report: a callable that cannot accept zero
        // supplied arguments is the property-context mismatch naming its true minimum
        // supply, and a clause family keeps its ordinary dispatch failure.
        if (resolvedAlgorithm is not Algorithm.Alias
            && ZeroArgumentValueDemandRejection(ZeroArgumentDemandShape.Property, name, span, resolvedAlgorithm) is { } rejection)
            return rejection;

        var propertyR = WithPropertyContextOnMissingOutput(
            resolvedR.Value.Binding.Name,
            span,
            resolvedAlgorithm,
            await ReadValueBindingCountedAsync(resolvedR.Value, ctx, valEnv).ConfigureAwait(false));

        return propertyR.IsError
            ? propertyR.Error
            : EvalResult<CountedResult?>.Ok(propertyR.Value);
    }

    // ── Main dispatch twin ──────────────────────────────────────────────────

    /// <summary>
    /// MIRROR OF <see cref="EvalParamCounted"/> — identical by construction. The
    /// parameter's supplied cell is demanded through the async seam
    /// (<see cref="NeedCell.DemandAsync"/>): its first VALUE demand evaluates the supplied
    /// computation once and every later read reuses that outcome (AT-MOST-ONCE ARGUMENT
    /// VALUE EVALUATION). Every other tier is a lookup with no child evaluation, read by
    /// the synchronous twin.
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
            // MIRROR — a call reference never reaches host code.
            if (HostArgumentBoundaryError(valueR.Value, ctx.Budget, ctx.Observations?.StructuralTraversal) is { } refused) return refused;
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

        if (TryInvokeMetaReceiver(hostOperation, argNames, ctx) is { } metaReceived)
            return metaReceived;

        var argumentsR = await CollectHostOperationArgumentsAsync(argNames, ctx, valEnv).ConfigureAwait(false);
        if (argumentsR.IsError) return argumentsR.Error;

        var value = implementation(argumentsR.Value, ctx.Budget.CancellationToken);
        return NormalizeHostOperationValue(hostOperation, value, ctx.Budget, ctx.Observations?.StructuralTraversal);
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

            // An interpolated string's hole may await an asynchronous host operation, so it is
            // driven by the machine twin like every spine kind (never a sync-delegable leaf).
            Expr.Unary or Expr.Binary or Expr.Comparison or Expr.Index or Expr.ListLiteral or Expr.InterpolatedString
                => await EvalExpressionSpineCountedAsync(expr, ctx, valEnv).ConfigureAwait(false),

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

        var resolvedR = await LookupLexicalForValueAsync(ctx.CallStack[0], name, ctx).ConfigureAwait(false);
        if (resolvedR.IsError)
            return AtSpanIfMissing(resolvedR.Error, span);

        if (resolvedR.Value.ResolvedAlgorithm is not Algorithm.Alias
            && ZeroArgumentValueDemandRejection(ZeroArgumentDemandShape.Property, name, span, resolvedR.Value.ResolvedAlgorithm) is { } rejection)
            return rejection;

        var propertyR = WithPropertyContextOnMissingOutput(resolvedR.Value.Binding.Name, span, resolvedR.Value.ResolvedAlgorithm,
            await ReadValueBindingCountedAsync(resolvedR.Value, ctx, valEnv).ConfigureAwait(false));
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
                            link.Op, previousOperand, link.Operand, frames[top].FirstValue!, pendingChild.Value, frames[top].Node.Span, ctx);
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

                case Expr.Index selection:
                    {
                        // MIRROR of the sync Index case: the receiver once, the supply formed
                        // (spreads only), the supplied selectors left to right through the ONE
                        // AdvanceSelection step, then the capture.
                        if (frames[top].Phase == 0)
                        {
                            if (!hasPendingChild)
                            {
                                requestedChild = selection.Target;
                                break;
                            }

                            hasPendingChild = false;
                            frames[top].FirstValue = pendingChild.Value;
                            frames[top].Phase = 1;
                            if (HasSpreadSelector(selection.Selectors))
                            {
                                var formed = await FormSelectionSupply(selection, ctx, valEnv, asynchronous: true).ConfigureAwait(false);
                                if (formed.IsError)
                                {
                                    completed = formed.Error;
                                    break;
                                }

                                frames[top].Selection = formed.Value;
                            }
                        }

                        completed = AdvanceSelection(ref frames[top], hasPendingChild ? pendingChild.Value : null, ctx, out requestedChild, out var selectorCell, out var viewIndex);
                        hasPendingChild = false;
                        if (selectorCell is not null)
                        {
                            var demanded = await selectorCell.DemandAsync().ConfigureAwait(false);
                            completed = demanded.IsError
                                ? SelectorFailure(demanded.Error, frames[top])
                                : AdvanceSelection(ref frames[top], demanded.Value.Value, ctx, out requestedChild, out _, out viewIndex);
                        }

                        // MIRROR of the sync machine's argument-view step (S2): the view's cells, the ONE
                        // cell at the validated position, its demand, then its acceptance.
                        if (viewIndex >= 0)
                        {
                            var view = (Result.CallReference)frames[top].FirstValue!;
                            var viewCells = await PrepareArgumentViewAsync(view, ctx).ConfigureAwait(false);
                            var viewCell = ArgumentViewSelectionCell(viewCells, viewIndex, frames[top]);
                            if (viewCell.IsError)
                                completed = viewCell.Error;
                            else
                            {
                                var viewValue = await viewCell.Value.DemandAsync().ConfigureAwait(false);
                                completed = AcceptArgumentViewSelection(ref frames[top], viewValue, ctx);
                            }
                        }

                        break;
                    }

                case Expr.ListLiteral(var elements):
                    {
                        frames[top].ListItems ??= NewListSlots(elements);
                        if (hasPendingChild)
                        {
                            // WRITTEN-SLOT REIFICATION: a machine-kind element is never a
                            // spread, so its counted supply contributes exactly ONE value.
                            hasPendingChild = false;
                            AddListSlot(frames[top].ListItems!, pendingChild.Value, ctx.Budget);
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

                            // Transient-bounded before it grows (SEC-01); mirrors the sync machine.
                            AddListSlots(frames[top].ListItems!, slotsR.Value, ctx.Budget, element is Expr.SequenceSpread);
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
                        if (ReserveCollection(ctx, ListSlotTotal(frames[top].ListItems!), frames[top].Node.Span) is { } limitError)
                        {
                            completed = limitError;
                            break;
                        }

                        completed = EvalResult<CountedResult>.Ok(new CountedResult(
                            Result.ListValue.TakeOwnership(frames[top].ListItems!.ToArray()), 1));
                        break;
                    }

                case Expr.InterpolatedString(var head, var links):
                    {
                        if (frames[top].Text is null)
                        {
                            frames[top].Text = new InterpolatedTextBuilder(ctx.Budget);
                            if (!frames[top].Text!.Append(head))
                            {
                                completed = frames[top].Text!.LimitError(frames[top].Node.Span);
                                break;
                            }
                        }
                        else
                        {
                            // The hole of link Phase just arrived: its text, then the link's text.
                            hasPendingChild = false;
                            if (InterpolationHoleRefusal(pendingChild.Value, links[frames[top].Phase].Hole) is { } refusedHole)
                            {
                                completed = refusedHole;
                                break;
                            }
                            if (!frames[top].Text!.AppendValue(pendingChild.Value)
                                || !frames[top].Text!.Append(links[frames[top].Phase].Text))
                            {
                                completed = frames[top].Text!.LimitError(frames[top].Node.Span);
                                break;
                            }

                            frames[top].Phase++;
                        }

                        if (frames[top].Phase < links.Count)
                        {
                            requestedChild = links[frames[top].Phase].Hole;
                            break;
                        }

                        completed = frames[top].Text!.Complete(frames[top].Node.Span);
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
                    if (decorateTopFrame)
                        error = DecorateSpineChildError(error, frames[frameCount - 1]);

                    decorateTopFrame = true;
                    frameCount--;
                }

                // MIRROR: a missing output escaping the spine is nested (Q-36).
                return NestMissingOutput(error);
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
            var materialized = await MaterializeRequiredRegionAsync(region, ctx).ConfigureAwait(false);
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
        TransientSupply bound = default;

        foreach (var expr in rows)
        {
            var countedR = await EvalCountedAsync(expr, rowCtx, valEnv).ConfigureAwait(false);
            // A row is a SUBORDINATE computation of the body or capture (Q-36).
            if (countedR.IsError) return NestMissingOutput(countedR.Error);

            // The row-slot accumulator is transient-bounded BEFORE it grows (SEC-01): once `(A*, A*)`
            // passes the limit the remaining rows are formed count-only and the capture's own
            // reservation below refuses the full size.
            if (expr is Expr.SequenceSpread)
            {
                AddCountedTopLevelValuesBounded(results, countedR.Value, reserveCtx.Budget, ref bound, expansion: true);
                emittedCount += countedR.Value.EmittedCount;
                continue;
            }

            // A non-spread output expression is always one visible output slot,
            // even when it evaluates to the empty sequence value `()`.
            AddSlotBounded(results, countedR.Value.Value, reserveCtx.Budget, ref bound);
            emittedCount += countedR.Value.EmittedCount == 0 ? 1 : countedR.Value.EmittedCount;
        }

        if (bound.Overflowed)
            return RefuseOverflowedCaptureAtRows(reserveCtx.Budget, bound, rows);
        var capturedR = MakeCheckedSequenceCaptureAtRows(reserveCtx.Budget, results, rows);
        if (capturedR.IsError) return capturedR.Error;

        var counted = new CountedResult(capturedR.Value, emittedCount);
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

        if (OutputRowsAccessError(alg) is { } accessError)
            return accessError;

        var slots = new List<Result>();
        TransientSupply bound = default;
        SourceSpan? overflowAt = null;
        var pushedCtx = EnterAlgorithmBody(alg, ctx, valEnv, parameterNames);
        foreach (var expr in alg.Output)
        {
            var countedR = await EvalCountedAsync(expr, pushedCtx, valEnv).ConfigureAwait(false);
            if (countedR.IsError) return countedR.Error;
            AddOutputRowItems(slots, expr, countedR.Value, ctx.Budget, ref bound, ref overflowAt);
        }

        return bound.Overflowed
            ? RefuseTransientSupply(ctx.Budget, bound, overflowAt)
            : EvalResult<IReadOnlyList<Result>>.Ok(slots);
    }

    /// <summary>MIRROR OF <see cref="EvalWhileVerdictSlots"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<IReadOnlyList<Result>?>> EvalWhileVerdictSlotsAsync(
        Algorithm alg,
        EvalCtx ctx,
        ValEnv valEnv,
        IReadOnlyList<string>? parameterNames = null)
    {
        if (alg is Algorithm.Builtin(var builtin))
        {
            var countedR = EvalBuiltinValueCounted(builtin);
            return countedR.IsError ? countedR.Error : WhileVerdictOfSupply([countedR.Value.Value]);
        }

        if (OutputRowsAccessError(alg) is { } accessError)
            return accessError;

        var rows = alg.Output;
        var slots = new List<Result>(rows.Count);
        var pushedCtx = EnterAlgorithmBody(alg, ctx, valEnv, parameterNames);
        var flagRow = rows.Count - 1;
        CountedResult flagRowValue = default;
        TransientSupply discovery = default;
        SourceSpan? overflowAt = null;
        for (; flagRow >= 0; flagRow--)
        {
            var countedR = await EvalCountedAsync(rows[flagRow], pushedCtx, valEnv).ConfigureAwait(false);
            if (countedR.IsError) return countedR.Error;
            AddOutputRowItems(slots, rows[flagRow], countedR.Value, ctx.Budget, ref discovery, ref overflowAt);
            // A flag row whose items alone pass the ceiling cannot be read (SEC-01).
            if (discovery.Overflowed)
                return RefuseTransientSupply(ctx.Budget, discovery, overflowAt);
            if (slots.Count != 0)
            {
                flagRowValue = countedR.Value;
                break;
            }
        }

        if (flagRow < 0)
            return new EvalError.WithContext(WhileStepWithoutFlagContext, new EvalError.BadArity());
        var flag = ContinuationFlagOfRow(rows[flagRow], slots[^1]);
        if (flag.IsError) return flag.Error;
        if (!flag.Value) return EvalResult<IReadOnlyList<Result>?>.Ok(null);

        if (flagRow > 0)
        {
            slots.Clear();
            TransientSupply bound = default;
            for (var i = 0; i < flagRow; i++)
            {
                var countedR = await EvalCountedAsync(rows[i], pushedCtx, valEnv).ConfigureAwait(false);
                if (countedR.IsError) return countedR.Error;
                AddOutputRowItems(slots, rows[i], countedR.Value, ctx.Budget, ref bound, ref overflowAt);
            }
            AddOutputRowItems(slots, rows[flagRow], flagRowValue, ctx.Budget, ref bound, ref overflowAt);
            if (bound.Overflowed)
                return RefuseTransientSupply(ctx.Budget, bound, overflowAt);
        }

        return EvalResult<IReadOnlyList<Result>?>.Ok(WhileNextStateSlots(slots));
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
        // SEC-01: an overflowed group forms count-only; its owner's reservation refuses the full size.
        TransientSupply bound = default;
        foreach (var expr in rows)
        {
            var exprSlotsR = await EvalExplicitSequenceValueExprSlotsAsync(expr, rowCtx, valEnv).ConfigureAwait(false);
            // A row is a SUBORDINATE computation of the body or capture (Q-36).
            if (exprSlotsR.IsError) return NestMissingOutput(exprSlotsR.Error);
            AddSlotsBounded(slots, exprSlotsR.Value, rowCtx.Budget, ref bound, expr is Expr.SequenceSpread);
        }

        return bound.Overflowed
            ? RefuseOverflowedCaptureAtRows(rowCtx.Budget, bound, rows)
            : EvalResult<IReadOnlyList<Result>>.Ok(slots);
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

            return MakeCheckedUnfoldedSlot(ctx.Budget, nestedItemsR.Value, expr, captureBody);
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

                return MakeCheckedUnfoldedSlot(ctx.Budget, nestedItemsR.Value, expr, wired.Output);
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
        var countedR = EntersInDeclaringContext(resolvedAlgorithm)
            ? await EvalPropertyOwnerBodyCountedAsync(resolvedAlgorithm, ctx, valEnv).ConfigureAwait(false)
            : await EvalZeroArgumentDemandOutputCountedAsync(resolvedAlgorithm, ctx, valEnv).ConfigureAwait(false);
        if (countedR.IsError)
            return countedR.Error;

        return EvalResult<ZeroArgPropertyResult>.Ok(
            new ZeroArgPropertyResult(countedR.Value.Value, countedR.Value.EmittedCount));
    }

    /// <summary>MIRROR OF <see cref="EvalPropertyOwnerBodyCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalPropertyOwnerBodyCountedAsync(
        Algorithm algorithm,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        if (algorithm.ParameterPatterns.Count != 0)
            return await EvalCollectingPropertyOwnerBodyCountedAsync(algorithm, ctx, valEnv).ConfigureAwait(false);

        if (OutputRowsAccessError(algorithm) is { } accessError)
            return accessError;

        var bodyCtx = EnterAlgorithmBody(algorithm, ctx, valEnv,
            inheritedBindingIdentity: PropertyReadBindingIdentity(algorithm, ctx, valEnv));
        var preparedR = await EvalOutputRowsPreparedCoreAsync(algorithm.Output, bodyCtx, ctx, valEnv).ConfigureAwait(false);
        return preparedR.IsError
            ? preparedR.Error
            : EvalResult<CountedResult>.Ok(preparedR.Value.Counted);
    }

    /// <summary>MIRROR OF <see cref="EvalCollectingPropertyOwnerBodyCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalCollectingPropertyOwnerBodyCountedAsync(
        Algorithm algorithm,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        // Binding the EMPTY supply cannot suspend — there are no arguments to evaluate — so the
        // twins share the one synchronous binder, as the demand funnel's twins do.
        var bindingsR = BindZeroArgumentSupply(algorithm, ctx);
        if (bindingsR.IsError) return bindingsR.Error;

        if (OutputRowsAccessError(algorithm) is { } accessError)
            return accessError;

        var boundCtx = WithNeedBindings(ctx, bindingsR.Value!, algorithm.Params);
        var boundValues = ShadowValEnv(valEnv, algorithm.Params);
        var bodyCtx = EnterAlgorithmBody(algorithm, boundCtx, boundValues,
            inheritedBindingIdentity: PropertyReadBindingIdentity(algorithm, ctx, valEnv));
        var preparedR = await EvalOutputRowsPreparedCoreAsync(algorithm.Output, bodyCtx, boundCtx, boundValues).ConfigureAwait(false);
        return preparedR.IsError
            ? preparedR.Error
            : EvalResult<CountedResult>.Ok(preparedR.Value.Counted);
    }

    /// <summary>MIRROR OF <see cref="GetOrEvaluateZeroArgPropertyResult"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<ZeroArgPropertyResult>> GetOrEvaluateZeroArgPropertyResultAsync(
        PropertyDeclaringOwner owner,
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
        PropertyDeclaringOwner owner,
        Property binding,
        ZeroArgPropertyAccessKind accessKind,
        Algorithm resolvedAlgorithm,
        EvalCtx ctx,
        ValEnv valEnv)
    {
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
            ZeroArgPropertyReadExecution(owner, binding, accessKind, resolvedAlgorithm, ctx, valEnv),
            () => EvaluateZeroArgPropertyResultAsync(resolvedAlgorithm, ctx, valEnv)).ConfigureAwait(false);
    }

    /// <summary>MIRROR OF <see cref="EvalZeroArgPropertyAccessCounted(PropertyDeclaringOwner, Property, ZeroArgPropertyAccessKind, Algorithm, EvalCtx, IReadOnlyList{ValueTuple{string, Result}})"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalZeroArgPropertyAccessCountedAsync(
        PropertyDeclaringOwner owner,
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
    /// propagate unchanged; the invocation runs inside the wrapper call's already-charged region.
    /// Argument scanning and return admission charge their structural work through the shared
    /// boundaries, exactly as synchronous dispatch does.
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

        // Shared canonical-value and admission boundary (null contract included) — see
        // NormalizeHostOperationValue; a cancelled-while-suspended run was already
        // honored above, so only genuinely successful values are normalized and admitted.
        var normalizedR = NormalizeHostOperationValue(hostOperation, value, ctx.Budget, ctx.Observations?.StructuralTraversal);
        if (normalizedR.IsError) return normalizedR.Error;
        var normalized = normalizedR.Value;
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
        // META-S3-1: a callee spelled `X.Algorithm` (see the synchronous twin).
        if (IsAlgorithmEdgeCallee(func))
            return await EvalAlgorithmCalleeCallCountedAsync((Expr.DotCall)func, args, ctx, valEnv).ConfigureAwait(false);

        var diagnosticName = CallDiagnosticName.FromExpression(func);
        // META-S3-0b: the ONE callee law through the async resolution adapter.
        var calleeR = await ResolveCalleeAsync(func, ctx).ConfigureAwait(false);
        if (calleeR.IsError)
            return CalleeResolutionFailure(diagnosticName, ctx, calleeR.Error);

        // MIRROR — CACHE-PUB-1: the origin-carrying dispatch of a possibly zero-supply call.
        if (MayFormZeroSupply(args) && TakesOriginDispatch(calleeR.Value))
            return WithCallCtx(
                diagnosticName,
                ctx,
                await EvalOriginCallCountedAsync(CalleeOrigin.Written(func), calleeR.Value, args, ctx, valEnv, diagnosticName).ConfigureAwait(false));

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
            return NestMissingOutput(await ApplyBuiltinCountedResolvedAsync(builtinId, argAlgsR.Value, ctx, valEnv).ConfigureAwait(false));
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
            && await TryProjectSharedDeconstructionTargetAsync(helper, target, args, ctx, valEnv).ConfigureAwait(false) is { } projected)
            return projected.IsError ? projected.Error : EvalResult<CountedResult>.Ok(new(projected.Value, projected.Value.ValueCount()));
        return await EvalNeedUserBody(callee, args, ctx, valEnv, calleeName, asynchronous: true).ConfigureAwait(false);
    }

    /// <summary>MIRROR OF <see cref="TryProjectSharedDeconstructionTarget"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<Result>?> TryProjectSharedDeconstructionTargetAsync(
        Algorithm.User helper,
        AssignmentDeconstructionTarget target,
        OutputBundle args,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        if (DeconstructionProjectionName(helper, target) is not { } name)
            return null;
        var boundR = SharedDeconstructionBind(helper, target, args, ctx, valEnv) is { } shared
            ? await ctx.DeconstructionBindingCache.GetOrBindAsync(shared,
                () => BindNeedDeconstruction(helper, args, ctx, valEnv, asynchronous: true)).ConfigureAwait(false)
            : await BindNeedDeconstruction(helper, args, ctx, valEnv, asynchronous: true).ConfigureAwait(false);
        if (boundR.IsError) return boundR.Error;
        return ProjectCountedValue(await boundR.Value[name].DemandAsync().ConfigureAwait(false));
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

        // Supplied cells — see the synchronous twin.
        var args = resolvedArgs;

        // META binding first — see the synchronous twin.
        if (BuiltinRegistry.GetBuiltin(builtin) is { DeclaresMetaParameter: true } metaBuiltin)
            return await ApplyMetaBuiltinCounted(metaBuiltin, args, ctx, valEnv, asynchronous: true).ConfigureAwait(false);

        switch (builtin, args.Count)
        {
            // `tick()` — see the synchronous twin (the primitive itself never awaits).
            case (BuiltinId.@tick, 0):
                return ExecuteTick(ctx);

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
        if (arg.Algorithm is not { } algorithm)
            return new EvalError.BadArity();

        // The ONE zero-argument value-demand law decides before any body (or the argument
        // level) is entered — see the synchronous twin.
        if (ZeroArgumentValueDemandError(arg.Source, algorithm) is { } rejection)
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

    /// <summary>MIRROR OF <see cref="DemandSequenceBuiltinCallItemValue"/> — keep in lock-step.</summary>
    private static async ValueTask<VariadicCallItem> DemandSequenceBuiltinCallItemValueAsync(
        VariadicCallItem item,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        if (item.Cell is { } cell && item.Value is null && item.ValueError is null)
        {
            var result = await cell.DemandAsync().ConfigureAwait(false);
            return FinishNeedCallItemDemand(item, cell, result, ctx);
        }

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
            : item with { Value = demandedR.Value.Value };
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
        // Call-item assembly evaluates nothing, so both engines share it.
        var items = BuildCallableCallItems(args);

        // Collection builtins are ordinary fixed-arity callables — see the synchronous twin.
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

        // An argument view bound as the whole collection (CallReference S2) — see the synchronous twin.
        if (collectionItem.Value is Result.CallReference { IsArgumentView: true } view)
            return ReadsArgumentView(builtin)
                ? EvalResult<BoundSequenceBuiltinArguments>.Ok(new BoundSequenceBuiltinArguments(default!, [], [], view))
                : ArgumentViewUnsupported(builtin);

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
        if (boundR.Value.ArgumentView is { } argumentView)
            return await EvalArgumentViewBuiltinAsync(builtin, argumentView, ctx).ConfigureAwait(false);

        // Deconstructed before the local functions capture them — see the synchronous twin.
        var (preparedInput, iterationItems, suffixArgs, _) = boundR.Value;

        // The pure per-builtin execution helpers are shared with the synchronous twin;
        // only the callback-driven builtins (filter, map, reduce) await.
        EvalResult<CountedResult> WithPreparedFlatItems(
            Func<IReadOnlyList<Result>, EvalResult<CountedResult>> handler)
            => handler(preparedInput.FlattenedItems);

        EvalResult<CountedResult> WithPreparedNumericItems(
            Func<IReadOnlyList<Decimal128>, EvalResult<CountedResult>> handler)
        {
            var numbersR = ExpectPreparedNumericItems(builtin, preparedInput);
            if (numbersR.IsError) return numbersR.Error;

            return handler(numbersR.Value);
        }

        switch (builtin)
        {
            case BuiltinId.@filter:
                {
                    if (iterationItems.Count == 0) return MakeCollectionListResult(ctx, []);
                    // META-S3-0b: the ONE synchronous slot projection; its awaited outcome is consumed by the async resolution.
                    var predicateR = await ExpectPreparedAlgorithmSuffixArgAsync(builtin, metadata.SuffixArgs, suffixArgs, 0, ctx).ConfigureAwait(false);
                    if (predicateR.IsError) return predicateR.Error;

                    return await EvalFilterCountedAsync(iterationItems, predicateR.Value, ctx, valEnv).ConfigureAwait(false);
                }

            case BuiltinId.@map:
                {
                    if (iterationItems.Count == 0) return MakeCollectionListResult(ctx, []);
                    // META-S3-0b: the ONE synchronous slot projection; its awaited outcome is consumed by the async resolution.
                    var transformR = await ExpectPreparedAlgorithmSuffixArgAsync(builtin, metadata.SuffixArgs, suffixArgs, 0, ctx).ConfigureAwait(false);
                    if (transformR.IsError) return transformR.Error;

                    return await EvalMapCountedAsync(iterationItems, transformR.Value, ctx, valEnv).ConfigureAwait(false);
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
                        suffixArgs,
                        0);
                    if (searchedItemR.IsError) return searchedItemR.Error;

                    return WithPreparedFlatItems(items => EvalContainsCounted(ctx, items, searchedItemR.Value));
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
                        suffixArgs,
                        0);
                    if (countR.IsError) return countR.Error;

                    return WithPreparedFlatItems(items => EvalTakeCounted(ctx, items, countR.Value));
                }

            case BuiltinId.@skip:
                {
                    var countR = ExpectPreparedWholeNumberSuffixArg(
                        builtin,
                        metadata.SuffixArgs,
                        suffixArgs,
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
                        suffixArgs,
                        1);
                    if (initialR.IsError) return initialR.Error;
                    if (iterationItems.Count == 0) return EvalResult<CountedResult>.Ok(new(initialR.Value, initialR.Value.ValueCount()));

                    // META-S3-0b: the ONE synchronous slot projection; its awaited outcome is consumed by the async resolution.
                    var stepR = await ExpectPreparedAlgorithmSuffixArgAsync(builtin, metadata.SuffixArgs, suffixArgs, 0, ctx).ConfigureAwait(false);
                    if (stepR.IsError) return stepR.Error;

                    return await EvalReduceCountedAsync(
                        iterationItems,
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

            // The step's ordinary call result, whole, with its value-boundary count (HO-03).
            accumulator = ReCountValueBoundary(stepR.Value);
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

            // The transform's ordinary call result is ONE element (HO-03).
            mapped.Add(transformR.Value.Value);
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

        // META-S3-0b: receiver navigation can project a parameter's cell — resolved asynchronously.
        var navigated = await ResolveDotReceiverAsync(target, ctx).ConfigureAwait(false);
        if (navigated.IsError && !IsAbsentIdentity(navigated.Error))
            return navigated.Error;
        var targetAlg = navigated.IsError ? null : navigated.Value.Receiver;
        var receiverIsStructuralMember = navigated.IsOk && navigated.Value.IsStructuralMember;

        // MIRROR — ONE structural lookup decides the route (SelectDotEdge); a member named `string` wins too.
        if (SelectDotEdge(dotCall, targetAlg, ctx, out var route, out var prop) is { } selectionError)
            return selectionError;

        if (route == DotEdgeRoute.Member)
        {
            var wired = ChildOfInContext(targetAlg!, prop!.Value, ctx);
            // MIRROR — a member that is an alias is read and called as its target.
            if (wired is Algorithm.Alias)
                return await EvalAliasMemberCountedAsync(targetAlg!, prop, wired, argsOpt, name, ctx, valEnv).ConfigureAwait(false);
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
                                targetAlg!, prop, ZeroArgPropertyAccessKind.CountedStructural, simpleCallee, ctx, valEnv).ConfigureAwait(false)))
                        : ZeroArgumentDemandArityMismatch(simpleCallee);
                }

                if (AcceptsZeroArgumentValueDemand(wired))
                    return MarkSelectedMemberOutput(ReCountValueBoundary(
                        await EvalZeroArgPropertyAccessCountedAsync(
                            targetAlg!, prop, ZeroArgPropertyAccessKind.CountedStructural, wired, ctx, valEnv).ConfigureAwait(false)));

                if (wired is Algorithm.Conditional)
                    return new EvalError.NoMatchingBranch(name);

                return ZeroArgumentDemandArityMismatch(wired);
            }

            // MIRROR — CACHE-PUB-1: a possibly zero-supply member call names the selected member binding.
            if (MayFormZeroSupply(argsOpt) && TakesOriginDispatch(wired))
                return await EvalOriginCallCountedAsync(CalleeOrigin.Bound(targetAlg!, prop), wired, argsOpt, ctx, valEnv,
                    CallDiagnosticName.FromKnown(name)).ConfigureAwait(false);

            return await EvalResolvedCallCountedAsync(
                wired,
                argsOpt,
                ctx,
                valEnv,
                CallDiagnosticName.FromKnown(name)).ConfigureAwait(false);
        }

        // MIRROR — a structural miss: the intrinsics, or the extension call.
        switch (route)
        {
            case DotEdgeRoute.StringIntrinsic:
            {
                if (await RejectDotStringIntrinsicArgumentsAsync(argsOpt, ctx, valEnv).ConfigureAwait(false) is { } arityRejection)
                    return arityRejection;
                Result value;
                if (targetAlg is null)
                {
                    // The synchronous twin evaluates the value-only target with plain
                    // Eval; the counted twin's value projection is the same value.
                    var valCountedR = await EvalCountedAsync(target, ctx, valEnv).ConfigureAwait(false);
                    if (valCountedR.IsError) return NestMissingOutput(valCountedR.Error);
                    value = valCountedR.Value.Value;
                }
                else if (targetAlg is Algorithm.Alias)
                {
                    // MIRROR — the `.string` receiver is judged on the alias's target.
                    return await EvalAliasDotStringCountedAsync(target, targetAlg, receiverIsStructuralMember, ctx, valEnv).ConfigureAwait(false);
                }
                else
                {
                    var val = NestMissingOutput(await EvalDotStringReceiverAlgOutputAsync(target, targetAlg, receiverIsStructuralMember, ctx, valEnv).ConfigureAwait(false));
                    if (val.IsError) return val.Error;
                    value = val.Value;
                }
                var outR = ResultToString(ctx, value);
                if (outR.IsError) return outR.Error;
                return EvalResult<CountedResult>.Ok(new CountedResult(outR.Value, outR.Value.ValueCount()));
            }
            case DotEdgeRoute.InvokeIntrinsic:
                return targetAlg is null
                    ? await EvalDotInvokeValueReceiverCountedAsync(dotCall, ctx, valEnv).ConfigureAwait(false)
                    : await EvalDotInvokeIntrinsicCountedAsync(dotCall, targetAlg, receiverIsStructuralMember, ctx, valEnv).ConfigureAwait(false);
            case DotEdgeRoute.ArgumentsIntrinsic:
                return targetAlg is null
                    ? await EvalDotArgumentsValueReceiverCountedAsync(dotCall, ctx, valEnv).ConfigureAwait(false)
                    : await EvalDotArgumentsIntrinsicCountedAsync(dotCall, targetAlg, receiverIsStructuralMember, ctx, valEnv).ConfigureAwait(false);
            case DotEdgeRoute.AlgorithmIntrinsic:
                return targetAlg is null
                    ? await EvalDotAlgorithmValueReceiverCountedAsync(dotCall, ctx, valEnv).ConfigureAwait(false)
                    : await EvalDotAlgorithmIntrinsicCountedAsync(dotCall, targetAlg, receiverIsStructuralMember, ctx, valEnv).ConfigureAwait(false);
            default:
                return await CallLexicalWithReceiverCountedAsync(dotCall, ctx, valEnv).ConfigureAwait(false);
        }
    }

    /// <summary>MIRROR OF <see cref="EvalDotReferenceIntrinsicReceiver"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<Result>> EvalDotReferenceIntrinsicReceiverAsync(
        Expr.DotCall dotCall, Algorithm targetAlg, bool receiverIsStructuralMember, EvalCtx ctx, ValEnv valEnv)
    {
        Algorithm? demandAlg = null;
        if (targetAlg is Algorithm.Alias alias)
        {
            var terminal = await ResolveAliasValueTerminalAsync(alias, ctx).ConfigureAwait(false);
            if (terminal.IsError) return terminal.Error;
            demandAlg = terminal.Value.Algorithm;
        }
        return NestMissingOutput(await EvalDotStringReceiverAlgOutputAsync(dotCall.Target, targetAlg, receiverIsStructuralMember, ctx, valEnv, demandAlg).ConfigureAwait(false));
    }

    /// <summary>MIRROR OF <see cref="EvalDotArgumentsIntrinsicCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalDotArgumentsIntrinsicCountedAsync(
        Expr.DotCall dotCall, Algorithm targetAlg, bool receiverIsStructuralMember, EvalCtx ctx, ValEnv valEnv)
    {
        if (RejectDotArgumentsIntrinsicArguments(dotCall.Args) is { } rejection)
            return rejection;
        var receiver = await EvalDotReferenceIntrinsicReceiverAsync(dotCall, targetAlg, receiverIsStructuralMember, ctx, valEnv).ConfigureAwait(false);
        return receiver.IsError ? receiver.Error : ArgumentsOfCallReferenceValue(receiver.Value, ctx);
    }

    /// <summary>MIRROR OF <see cref="EvalDotArgumentsValueReceiverCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalDotArgumentsValueReceiverCountedAsync(Expr.DotCall dotCall, EvalCtx ctx, ValEnv valEnv)
    {
        if (RejectDotArgumentsIntrinsicArguments(dotCall.Args) is { } rejection)
            return rejection;
        // The synchronous twin evaluates the value-only target with plain Eval; the counted twin's
        // value projection is the same value.
        var receiver = NestMissingOutput(await EvalCountedAsync(dotCall.Target, ctx, valEnv).ConfigureAwait(false));
        return receiver.IsError ? receiver.Error : ArgumentsOfCallReferenceValue(receiver.Value.Value, ctx);
    }

    /// <summary>MIRROR OF <see cref="RejectDotInvokeIntrinsicArguments"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalError?> RejectDotInvokeIntrinsicArgumentsAsync(OutputBundle? argsOpt, EvalCtx ctx, ValEnv valEnv)
        => argsOpt is null
            ? new EvalError.IllegalInEval(InvokeRequiresArgumentListMessage)
            : await RejectDotStringIntrinsicArgumentsAsync(argsOpt, ctx, valEnv).ConfigureAwait(false);

    /// <summary>MIRROR OF <see cref="EvalDotInvokeIntrinsicCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalDotInvokeIntrinsicCountedAsync(
        Expr.DotCall dotCall, Algorithm targetAlg, bool receiverIsStructuralMember, EvalCtx ctx, ValEnv valEnv)
    {
        if (await RejectDotInvokeIntrinsicArgumentsAsync(dotCall.Args, ctx, valEnv).ConfigureAwait(false) is { } rejection)
            return rejection;
        var receiver = await EvalDotReferenceIntrinsicReceiverAsync(dotCall, targetAlg, receiverIsStructuralMember, ctx, valEnv).ConfigureAwait(false);
        return receiver.IsError ? receiver.Error : await InvokeCallReferenceValueAsync(receiver.Value, ctx).ConfigureAwait(false);
    }

    /// <summary>MIRROR OF <see cref="EvalDotInvokeValueReceiverCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalDotInvokeValueReceiverCountedAsync(Expr.DotCall dotCall, EvalCtx ctx, ValEnv valEnv)
    {
        if (await RejectDotInvokeIntrinsicArgumentsAsync(dotCall.Args, ctx, valEnv).ConfigureAwait(false) is { } rejection)
            return rejection;
        // The synchronous twin evaluates the value-only target with plain Eval; the counted twin's
        // value projection is the same value.
        var receiver = NestMissingOutput(await EvalCountedAsync(dotCall.Target, ctx, valEnv).ConfigureAwait(false));
        return receiver.IsError ? receiver.Error : await InvokeCallReferenceValueAsync(receiver.Value.Value, ctx).ConfigureAwait(false);
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

        // META-S3-2: the fallback name may be a runtime-target alias, whose CALLABLE is awaited.
        var calleeR = await ResolveAsync(ctx, (fallbackName, ctx), static state => ResolveNamedAlgorithm(state.fallbackName, span: null, state.ctx)).ConfigureAwait(false);
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
        // META-S3-0b: a parameter fallback projects its cell — resolved asynchronously.
        var calleeR = await ResolveAsync(ctx, (dotCall.EffectiveLexicalFallback, ctx), static state => ResolveAlg(state.EffectiveLexicalFallback, state.ctx)).ConfigureAwait(false);
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
        ValEnv valEnv,
        Algorithm? demandAlg = null)
    {
        // A parameter bound to a supplied cell is a VALUE demand of that cell, reported as the
        // written argument reports it, before (and instead of) the zero-argument law — see the
        // synchronous twin.
        if (target is Expr.Param(var needName) && LookupNeed(ParameterContext(needName, ctx, ref valEnv).NeedEnv, needName) is not null)
            return ProjectCountedValue(await EvalParamCountedAsync(needName, target.Span, ctx, valEnv).ConfigureAwait(false));

        // Every other receiver is demanded for its VALUE with zero arguments through the ONE
        // law — see the synchronous twin (an alias receiver is judged on its VALUE terminal's algorithm).
        if (ZeroArgumentValueDemandError(target, demandAlg ?? targetAlg) is { } rejection)
            return rejection;

        // The accepted receiver is READ exactly as a value position reads it — see the
        // synchronous twin.
        switch (target)
        {
            case Expr.Param(var name):
                // MIRROR OF the synchronous twin: the ordinary value-position parameter read (a
                // parameter with a supplied cell returned above): its counted or bound value, and
                // BadArity for a binding that has only an algorithm channel, which is never evaluated.
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

        var resolvedR = await ResolveAsync(ctx, (owner: ctx.CallStack[0], name, ctx), static state => LookupLexicalRaw(state.owner, state.name, state.ctx)).ConfigureAwait(false);
        if (resolvedR.IsError)
            return AtSpanIfMissing(resolvedR.Error, target.Span);

        // MIRROR — a receiver reached THROUGH an alias reads its VALUE terminal.
        if (resolvedR.Value.ResolvedAlgorithm is Algorithm.Alias)
            return await EvalAliasDotStringLexicalReceiverAsync(target, resolvedR.Value, ctx, valEnv).ConfigureAwait(false);

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
        // META-S3-0b: the container's re-navigation goes through the async resolution adapter
        // too, so its correctness follows from the general rule (an awaited outcome is consumed
        // or replayed), not from an earlier navigation having completed the same projection.
        var navigated = await ResolveDotReceiverAsync(edge.Target, ctx).ConfigureAwait(false);
        if (navigated.IsOk && LookupPropBinding(navigated.Value.Receiver, edge.Name, ctx.Budget) is { } member)
        {
            if (TryEnterArgumentEvaluationLevel(ctx, out var level) is { } limitError)
                return limitError;

            using (level)
            {
                if (ChildOfInContext(navigated.Value.Receiver, member.Value, ctx) is Algorithm.Alias memberAlias)
                {
                    var terminal = await ResolveAliasValueTerminalAsync(memberAlias, ctx, member).ConfigureAwait(false);
                    return terminal.IsError
                        ? terminal.Error
                        : ProjectCountedValue(await ReadAliasTerminalCountedAsync(terminal.Value, ctx, valEnv).ConfigureAwait(false));
                }

                return ProjectCountedValue(await EvalZeroArgPropertyAccessCountedAsync(
                    navigated.Value.Receiver,
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
        var items = new List<Result>();
        // MIRROR OF the sync join: stream shared-AST occurrences and bound plain leaves too.
        TransientSupply bound = new() { HasExpansion = true };

        foreach (var leaf in leaves)
        {
            if (leaf is Expr.SequenceSpread)
            {
                // A spread leaf supplies exactly the spread EXPRESSION's items, read
                // back like a spread output row (see the synchronous twin).
                var spreadR = await EvalCountedAsync(leaf, ctx, valEnv).ConfigureAwait(false);
                // MIRROR: a leaf is a SUBORDINATE computation of the join (Q-36).
                if (spreadR.IsError) return NestMissingOutput(spreadR.Error);

                AddCountedTopLevelValuesBounded(items, spreadR.Value, ctx.Budget, ref bound, expansion: true);
                continue;
            }

            // The synchronous twin evaluates the leaf with plain Eval; the counted
            // twin's value projection is the same value.
            var valueR = await EvalCountedAsync(leaf, ctx, valEnv).ConfigureAwait(false);
            if (valueR.IsError) return NestMissingOutput(valueR.Error);

            if (valueR.Value.Value.ValueCount() != 0)
                AddSlotBounded(items, valueR.Value.Value, ctx.Budget, ref bound);
        }

        // SEC-01: an overflowed join was formed count-only; its reservation refuses the full size.
        if ((bound.Overflowed ? ReserveCollection(ctx, bound.Total) : ReserveSequenceCapture(ctx, items.Count)) is { } sequenceLimitError)
            return sequenceLimitError;

        var value = CombineOutputSlots(items);
        return EvalResult<CountedResult>.Ok(new CountedResult(
            value,
            value.ValueCount()));
    }

    /// <summary>MIRROR OF <see cref="EvalSequenceSpreadOperandValue"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<Result>> EvalSequenceSpreadOperandValueAsync(
        Expr expr,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        if (expr is Expr.Capture(var captureBody))
        {
            var captureSpan = PreferExpressionSpan(expr.Span, captureBody);
            var captureR = WithSpan(captureSpan, await EvalCaptureValueAsync(captureBody, ctx, valEnv).ConfigureAwait(false));
            if (captureR.IsError)
                return SpreadOperandFailure(expr, captureSpan, captureR.Error);

            return captureR;
        }

        if (expr is Expr.AlgorithmExpr(var alg))
        {
            if (alg is Algorithm.Alias)
                return await EvalAliasSpreadOperandValueAsync(expr, alg, ctx, valEnv).ConfigureAwait(false);

            var wired = WireToCaller(ctx, alg);
            var blockSpan = PreferExpressionSpan(expr.Span, wired.Output);
            // See the synchronous twin: a spread operand is a zero-argument value demand.
            if (ZeroArgumentValueDemandRejection(ZeroArgumentDemandShape.Block, name: null, blockSpan, wired) is { } rejection)
                return rejection;

            var blockR = await EvalZeroArgumentDemandOutputAsync(wired, ctx, valEnv).ConfigureAwait(false);
            if (blockR.IsError)
                return SpreadOperandFailure(expr, blockSpan, blockR.Error);

            return blockR;
        }

        // The synchronous twin evaluates the operand with plain Eval; the counted
        // twin's value projection is the same value.
        var outputR = await EvalCountedAsync(expr, ctx, valEnv).ConfigureAwait(false);
        if (outputR.IsError)
            return SpreadOperandFailure(expr, expr.Span, outputR.Error);

        return EvalResult<Result>.Ok(outputR.Value.Value);
    }

    /// <summary>MIRROR OF <see cref="EvalSequenceSpreadCounted"/> — keep in lock-step.</summary>
    private static async ValueTask<EvalResult<CountedResult>> EvalSequenceSpreadCountedAsync(
        Expr expr,
        EvalCtx ctx,
        ValEnv valEnv)
    {
        var operand = PeelSpreadLayers(expr, out var layers);
        var operandR = await EvalSequenceSpreadOperandValueAsync(operand, ctx, valEnv).ConfigureAwait(false);
        if (operandR.IsError) return operandR.Error;
        return OpenSpreadLayers(operandR.Value, layers, expr, ctx, transportView: false, out _);
    }
}
