using System.Diagnostics.CodeAnalysis;

namespace KatLang;

/// <summary>
/// [HOST] B2c — branch-lazy module loading. One conditional branch body whose subtree owns
/// at least one unresolved <c>load</c> directive is a DEFERRED MODULE-ELABORATION REGION:
/// initial module elaboration does not fetch, parse, elaborate, or budget-charge anything
/// under it, and the eager front end elaborates it only PROVISIONALLY (the same walks with
/// the diagnostics sink withheld, so binder and ancestor-parameter references become
/// <see cref="Expr.Param"/>s for the exposure summary channel while nothing that could
/// depend on the deferred modules' members is reported). When evaluation SELECTS the branch,
/// the region is materialized: its modules are loaded through the ordinary loader (same
/// cache, budget, policy, cycle detection, and diagnostics), and the raw body is then
/// elaborated by the ordinary detector, resolver, and exposure passes under the exact
/// contexts the eager passes recorded. Nested clause families inside the materialized body
/// are deferred again by the same rule, so laziness is recursive across conditional
/// boundaries. The materialized body is cached on the region for the lifetime of the
/// elaborated tree (the same lifetime as the loader's per-URL module cache).
///
/// <para><b>Where a region lives.</b> A region is carried BY the placeholder body that stands
/// for it in the elaborated tree — <see cref="Algorithm.DeferredRegion"/>, an
/// equality-transparent slot the record copy constructor copies — never by a side table
/// keyed on the body's identity. One region is one deferred branch OCCURRENCE: the loader
/// clones a fresh placeholder per load-bearing branch it defers (its own region object, even
/// when host branches share one raw body object, so region identity is NOT declaration
/// identity — every clone of one raw body keeps that body's <see cref="Algorithm.Declaration"/>),
/// and each rewriting front-end pass installs a FORK of the region it found — the same loader
/// facts plus the pass's own context, see <see cref="WithStructure"/> and <see cref="WithExposure"/> — on the output view it
/// produces for the placeholder, so a placeholder reached under two front-end contexts (a
/// shared host subtree, one module spliced at two sites) yields two independent regions, and
/// a branch body can never inherit the materialization of whichever context ran first. The
/// one pass that observes without rewriting, declaration validation, RECORDS its bindings on
/// the region the tree already carries (<see cref="RecordValidation"/>). Everything that
/// merely copies a placeholder — parent wiring, a parameter-list replacement, the flat-binder
/// equivalent of a one-clause family — is a view of the same occurrence and shares its
/// region object, and with it the one materialization; nothing has to remember to re-attach
/// anything.</para>
///
/// <para>Lean has no counterpart: its input model is an already-elaborated tree with no
/// external modules and no demand timing. Once materialized, the selected branch is the very
/// tree eager elaboration would have produced, so core semantics are unchanged — only host
/// dependency materialization (and the timing of module-load and demand-time elaboration
/// diagnostics) moves to the selection boundary.</para>
/// </summary>
internal sealed class DeferredModuleRegion
{
    private readonly Lock _runLock = new();
    private Algorithm? _materialized;
    private int _materializationAttempts;
    private MaterializationRun? _inFlight;
    // How many runs their last consumer abandoned, and a compact summary of the failure a host
    // token callback raised while the most recent one was cancelled (both guarded by the run
    // lock): test-observable abandonment state, never a decision input. The summary holds
    // strings and a count only — never the run, its tasks, token sources, or the exception
    // graph — because the region lives as long as the elaborated tree.
    private int _abandonedRuns;
    private AbandonmentFailureSummary? _lastAbandonmentFailure;

    // B16: the loader gate turns held by materialization work in the current execution
    // context, innermost first (see HeldGateTurn).
    private static readonly AsyncLocal<HeldGateTurn?> s_heldGateTurns = new();
    private ParameterPropertyCollisionValidator.ParameterBindings? _validation;

    internal DeferredModuleRegion(
        ModuleLoader loader,
        Algorithm rawBody,
        ModuleLoader.LoadContext context,
        int depth,
        int nestedTraversalBase,
        SourceSpan? importSite,
        int importDepth)
    {
        if (rawBody.DeferredRegion is not null)
            throw new ArgumentException("A deferred region's raw body is unelaborated source structure and carries no region.", nameof(rawBody));
        ArgumentOutOfRangeException.ThrowIfNegative(importDepth);

        Loader = loader;
        RawBody = rawBody;
        Context = context;
        Depth = depth;
        NestedTraversalBase = nestedTraversalBase;
        ImportSite = importSite;
        ImportDepth = importDepth;
    }

    // A fork: the same occurrence's loader facts and every context recorded so far, with
    // its OWN materialization state (a fork is made by the front end, before any evaluation).
    private DeferredModuleRegion(DeferredModuleRegion source)
    {
        Loader = source.Loader;
        RawBody = source.RawBody;
        Context = source.Context;
        Depth = source.Depth;
        NestedTraversalBase = source.NestedTraversalBase;
        ImportSite = source.ImportSite;
        ImportDepth = source.ImportDepth;
        _validation = source._validation;
        Exposure = source.Exposure;
        Structure = source.Structure;
    }

    /// <summary>The loader that deferred the region: its cache, budget, policy, and downloader.</summary>
    internal ModuleLoader Loader { get; }

    /// <summary>
    /// The branch body exactly as the loader found it — unelaborated, with its load directives
    /// and, by construction, no <see cref="Algorithm.DeferredRegion"/> of its own (the loader
    /// strips one before deferring a body that was itself a placeholder of an earlier
    /// elaboration), so a materialization derived from it by <c>with</c> copies is never a
    /// placeholder for anything.
    /// </summary>
    internal Algorithm RawBody { get; }

    /// <summary>The load context the family was reached under; the body inherits it, exactly as eager elaboration would apply it.</summary>
    internal ModuleLoader.LoadContext Context { get; }

    /// <summary>The body's counted traversal depth within its tree, so its loads are judged at the depth eager elaboration would have used.</summary>
    internal int Depth { get; }

    /// <summary>The live traversal base at deferral (non-zero when the family sits inside a loaded module).</summary>
    internal int NestedTraversalBase { get; }

    /// <summary>
    /// The live IMPORT DEPTH at deferral: how many module frames enclosed the family (0 for a
    /// family the current document wrote; for a family inside a materialized branch, the
    /// depth that materialization resumed plus the frames entered since). The materialization's
    /// walk resumes at this depth and restores the displaced one when it ends, so the body's
    /// loads obey <see cref="SourceProcessingLimits.MaxModuleDepth"/> — and a refusal names the
    /// depth — exactly as eager elaboration would. Forks copy it.
    /// </summary>
    internal int ImportDepth { get; }

    /// <summary>
    /// The import site the family was reached under (see <c>ModuleLoader._importSite</c>): null
    /// for a family the current document wrote, otherwise the span, in the current document,
    /// of the load directive that imported the module the family sits in. Restored as the
    /// loader's walk context while the region materializes, and the initial import-site
    /// anchor of every demand-time front-end pass over the loaded body, so a diagnostic raised
    /// inside module content — which carries no locations of its own — is positioned at the
    /// site this document wrote rather than at a module-relative coordinate or a sentinel.
    /// The site is a position in the document the recording loader serves (a loader and its
    /// module cache belong to ONE parse of ONE document — the pipeline creates a loader per
    /// document), which is what keeps every span a materialization reports in that
    /// document's coordinate space even for a family inside a cached module spliced twice.
    /// </summary>
    internal SourceSpan? ImportSite { get; }

    /// <summary>Installed by property-exposure resolution on its output view — the last eager pass, so the tree's final region carries every context.</summary>
    internal PropertyExposureResolver.DeferredBranchContext? Exposure { get; private init; }

    /// <summary>Recorded by declaration validation (see <see cref="RecordValidation"/>); carried by every later fork.</summary>
    internal ParameterPropertyCollisionValidator.ParameterBindings? Validation => _validation;

    internal StaticStructureDeferredContext? Structure { get; private init; }

    internal DeferredModuleRegion WithStructure(StaticStructureDeferredContext context)
        => new(this) { Structure = context };

    internal DeferredModuleRegion WithExposure(PropertyExposureResolver.DeferredBranchContext exposure)
        => new(this) { Exposure = exposure };

    /// <summary>
    /// Records the completed enclosing parameter bindings declaration validation held at the
    /// branch. Validation is an observation walk over a completed tree — it rewrites nothing,
    /// so there is no output view to install a fork on — and it runs before exposure
    /// resolution, whose fork carries the recording into the tree's final region. A later
    /// recording replaces an earlier one (a placeholder reached under two binding contexts of
    /// a shared host subtree keeps the last, as the registry it replaces did).
    /// </summary>
    internal void RecordValidation(ParameterPropertyCollisionValidator.ParameterBindings validation)
        => _validation = validation;

    /// <summary>Completed materializations plus failed attempts; test-observable, never a decision input.</summary>
    internal int MaterializationAttempts => Volatile.Read(ref _materializationAttempts);

    /// <summary>
    /// Consumers counted on the in-flight run (zero when none is in flight); read without the
    /// run lock, so it is test-observable only, never a decision input.
    /// </summary>
    internal int InFlightConsumers => Volatile.Read(ref _inFlight)?.Consumers ?? 0;

    /// <summary>
    /// Runs abandoned because their LAST consumer left before completion (each one's work was
    /// cancelled exactly once by that leave); a leave that is not the last, and a run cancelled
    /// only by the source-processing token, abandon nothing. Test-observable only, never a
    /// decision input.
    /// </summary>
    internal int AbandonedRuns
    {
        get { lock (_runLock) return _abandonedRuns; }
    }

    /// <summary>
    /// What the most recently abandoned run recorded while its last consumer's leave cancelled
    /// it: a bounded summary of the failure a host token callback raised out of that
    /// cancellation (see <see cref="AbandonmentFailureSummary"/>), or <c>null</c> when the
    /// cancellation completed normally or no run was abandoned (<see cref="AbandonedRuns"/>
    /// tells the two apart). Each abandonment starts a fresh record, a later failure of an
    /// earlier run never overwrites it, and a successful retry leaves it as it is. Settled
    /// once the leave's <c>Cancel()</c> has returned — the token registration that performs the
    /// leave runs inside the host's own <c>Cancel()</c>. Test-observable only: the failure
    /// belongs to the abandoned work, so it is never reported to a consumer or a host.
    /// </summary>
    internal AbandonmentFailureSummary? LastAbandonmentFailure
    {
        get { lock (_runLock) return _lastAbandonmentFailure; }
    }

    /// <summary>
    /// A compact, immutable description of a host token-callback failure raised while an
    /// abandoned run was cancelled: the type of the exception <c>Cancel()</c> threw (normally
    /// <see cref="AggregateException"/>, nested once per linked token-source level), how many
    /// callback failures it carried once flattened, and the first one's type and bounded
    /// message. Strings and a count only, so it retains no exception, type, or host object.
    /// </summary>
    internal sealed record AbandonmentFailureSummary(
        string FailureType,
        int CallbackFailureCount,
        string FirstCallbackFailureType,
        string FirstCallbackFailureMessage)
    {
        /// <summary>The longest retained message or type name, in UTF-16 code units, before the truncation marker.</summary>
        internal const int MaxMessageLength = 256;

        internal static AbandonmentFailureSummary Of(Exception failure)
        {
            IReadOnlyList<Exception> callbacks = failure is AggregateException aggregate
                ? aggregate.Flatten().InnerExceptions
                : [failure];
            var first = callbacks.Count > 0 ? callbacks[0] : failure;
            string message;
            try
            {
                // Message is host-overridable. Diagnostic capture must not turn a callback's
                // failure into another exception escaping the host's Cancel().
                message = first.Message ?? "callback exception message unavailable";
            }
            catch (Exception)
            {
                message = "callback exception message unavailable";
            }
            if (message.Length > MaxMessageLength)
                message = string.Concat(message.AsSpan(0, ExprNameRenderer.SafePrefixLength(message, MaxMessageLength)), ExprNameRenderer.TruncationMarker);
            return new(TypeName(failure), callbacks.Count, TypeName(first), message);
        }

        private static string TypeName(Exception exception)
        {
            var name = exception.GetType().FullName ?? exception.GetType().Name;
            return name.Length > MaxMessageLength
                ? string.Concat(name.AsSpan(0, ExprNameRenderer.SafePrefixLength(name, MaxMessageLength)), ExprNameRenderer.TruncationMarker)
                : name;
        }
    }

    internal bool IsMaterialized => Volatile.Read(ref _materialized) is not null;

    internal bool TryGetMaterialized([NotNullWhen(true)] out Algorithm? body)
    {
        body = Volatile.Read(ref _materialized);
        return body is not null;
    }

    /// <summary>
    /// Materializes the region on demand: loads its modules through the owning loader, then
    /// runs the ordinary detector, resolver, and exposure passes over the loaded body under
    /// the recorded eager contexts. Serialized per loader (the loader processes one logical
    /// elaboration at a time, exactly as during initial elaboration), memoized on success,
    /// and NEVER memoized on failure: a failed or cancelled attempt leaves no partially
    /// elaborated body behind, and a later selection retries exactly like the module cache
    /// retries a failed download.
    ///
    /// <para><b>Accounting of an attempt.</b> The body's loads are judged at the import depth
    /// recorded at deferral (<see cref="ImportDepth"/>), as eager elaboration would judge them.
    /// An attempt that publishes nothing — whether its load failed, its body has a front-end
    /// error, a structural or stack refusal stopped it, or it was cancelled or abandoned during
    /// the load, the compile, or at publication — releases the cache-hit splices charged by its
    /// walk and by nested walks that did not enter the cache, exactly once, before the loader's gate is released
    /// (<see cref="ModuleLoader.ReleaseUnpublishedSplices"/>), so failed retries do not drain the
    /// aggregate. Downloads and their admitted source text stay charged. A module that was
    /// cached inside the attempt keeps its full weight, so its next splice
    /// charges again. Under an aggregate limit that exactly fits the program, a retry after such
    /// an attempt can therefore stay refused until the tree is parsed again — over-refusal
    /// only, by design. A published attempt keeps every charge: the program grew by them.</para>
    ///
    /// <para><b>Cancellation and shared demand.</b> A materialization exists only because an
    /// evaluation selected the branch, so the requesting evaluation's lifetime governs it:
    /// concurrent selections of one region share ONE underlying run (one gate turn, one
    /// download per module, one attempt), each consumer waits on it with its own
    /// <paramref name="evaluationCancellationToken"/>, and a cancelled consumer leaves at once
    /// with its own token's identity — without disturbing consumers that still need the
    /// result. The underlying work (the wait for the loader's turn, and the download and
    /// elaboration inside it) is cancelled exactly when its LAST consumer leaves; the loader
    /// links that with the host's source-processing token, which stays authoritative and keeps
    /// its identity for every consumer. A run cancelled that way publishes no region body; the next
    /// selection starts a fresh run, while already-completed dependency modules stay cached.</para>
    ///
    /// <para><b>Who runs the work, and how cancellation reaches it.</b> The consumer that starts
    /// a run executes it on its own stack, OUTSIDE the region's run lock, exactly as
    /// synchronously as the downloader allows: a synchronously completing downloader (or an
    /// already-cached module) completes the whole materialization on the calling thread, and
    /// after a genuine suspension the starter resumes wherever the downloader's awaitable
    /// completes. Every consumer — the starter included — registers its evaluation token for
    /// as long as it waits, and that registration performs the consumer's ordinary leave
    /// (idempotent per consumer, so the registration and the consumer's own exit never count
    /// twice): when the leaving consumer is the last, the run is cancelled at once, which
    /// reaches the downloader's token and the compile's cancellation checks even while the
    /// work is running inline on some consumer's thread. Joiners wait on the run's shared
    /// completion, whose continuations run asynchronously, so a consumer that joined during
    /// the starter's inline segment never resumes on the starter's stack. A consumer whose own
    /// thread is running the work cannot return before that work next observes cancellation,
    /// suspends, or ends; its leave still counts immediately, so if it was the last consumer
    /// the work has already been cancelled, and otherwise the work continues for the
    /// consumers that still wait. A failure raised by a host token callback while a leave
    /// cancels the run belongs to the abandoned run: it never replaces a consumer's
    /// <see cref="OperationCanceledException"/> and never escapes into the host's own
    /// <c>Cancel()</c>.</para>
    ///
    /// <para><b>Reentrant selection (B16 host contract, owner decision 2026-11-10; see
    /// <see cref="RunOptions.DownloadCode"/>, Reentrancy).</b> A load is in progress for the whole
    /// gate turn its work holds: every downloader call and the parse and elaboration of what it
    /// returns. A selection made in that turn's execution context — by the module downloader
    /// the turn is running, or by anything that downloader runs or starts while its execution
    /// context flows, synchronously or not — would wait for that turn: the same region's run
    /// (whose completion follows the download), or the gate itself (any other region of the
    /// loader). It is refused at once, without a token, as an ordinary
    /// <see cref="EvalError.ModuleRegionMaterializationFailed"/> carrying one
    /// <see cref="DiagnosticCode.LoadCycle"/> diagnostic — never as cancellation — after the
    /// cache check (a materialized region is always served) and after the established
    /// cancellation checks (the source-processing token, then the evaluation token). The
    /// refused selection counts no consumer, makes no attempt and charges nothing, so the held
    /// run, the gate, the cache, and later selections are unaffected. Concurrent consumers from
    /// any other context, an evaluation of a different tree, and a context that outlived its
    /// turn are never refused. The library cannot observe the reverse dependency (whether the
    /// downloader waits for the evaluation), so the refusal prevents a possible cycle without
    /// proving one: by contract it also refuses flowed work the downloader never waits for, and
    /// such work must start without the downloader's flowed context or after the load. A cycle
    /// the host builds outside that context is not caught.</para>
    /// </summary>
    internal async ValueTask<EvalResult<Algorithm>> MaterializeAsync(CancellationToken evaluationCancellationToken)
    {
        if (TryGetMaterialized(out var ready))
            return EvalResult<Algorithm>.Ok(ready);

        if (Structure is not { Forwardable: not null } || Validation is null || Exposure is null)
        {
            throw new InvalidOperationException(
                "Internal error: a deferred module region reached evaluation without its complete elaboration context. " +
                "The front-end pipeline carries every deferred branch through parameter detection, implicit-argument " +
                "resolution, declaration validation, and exposure resolution before a tree is evaluated.");
        }

        Loader.SourceProcessingCancellationToken.ThrowIfCancellationRequested();
        evaluationCancellationToken.ThrowIfCancellationRequested();

        // B16 host contract: a selection made in this loader's held gate turn's execution
        // context — by the downloader that turn is running, or by anything it started while that
        // context flowed — would wait for that very turn. Whether the downloader waits for the
        // selection is host code the library cannot observe, so every such selection is refused
        // now with an ordinary load-cycle error: a possible cycle is prevented, none is proven.
        // Nothing is counted, started, or charged: the region, the gate, and the held run are
        // untouched, and a later selection proceeds normally.
        if (IsInsideHeldGateTurn(Loader.MaterializationGate))
            return ReentrantMaterializationRejected();

        var consumer = JoinOrStartRun(out var starts);
        // Registered only once the consumer is counted: a token cancelled in the meantime runs
        // the leave synchronously here, so a run abandoned before it starts fails fast at the
        // loader gate without an attempt. A consumer's cancellation is its leave wherever its
        // thread is — including inside the work this consumer is about to run inline.
        var registration = evaluationCancellationToken.UnsafeRegister(
            static state => ((MaterializationConsumer)state!).Leave(), consumer);
        try
        {
            // The starter awaits the work itself, so after a genuine suspension it resumes where
            // the downloader's awaitable completes; joiners await the shared completion.
            var pending = starts ? StartRun(consumer.Run) : consumer.Run.Completion.Task;
            return await pending.WaitAsync(evaluationCancellationToken).ConfigureAwait(false);
        }
        catch (OperationCanceledException)
        {
            Loader.SourceProcessingCancellationToken.ThrowIfCancellationRequested();
            evaluationCancellationToken.ThrowIfCancellationRequested();
            throw;
        }
        finally
        {
            // Outside the run lock: disposing a registration waits for a callback that is running
            // on another thread, and that callback takes the lock.
            registration.Dispose();
            consumer.Leave();
        }
    }

    /// <summary>
    /// B16 — one loader gate turn held by materialization work, as seen from the execution
    /// context that work runs in. <see cref="RunCoreAsync"/> pushes a turn right after acquiring
    /// the gate and ends it before releasing it. The write is scoped to that async method, so
    /// the only code that can observe the turn is code running in the work's own execution
    /// context: the host downloader the work calls (the one piece of host code a gate turn
    /// runs), and whatever that downloader runs or starts in its flowed context (synchronous
    /// calls, await continuations, <see cref="Task.Run(Func{Task})"/> children). The starting
    /// evaluation never sees it once the work has returned or suspended, and neither does
    /// any consumer that joins from elsewhere.
    ///
    /// <para>Every materialization of the loader waits for its gate's current holder: a joiner
    /// of the holder's run waits for its completion, and any other run waits for the gate
    /// itself. A materialization requested while the current context still holds a turn on
    /// the same gate therefore waits for that turn. It is a genuine wait-for cycle only when
    /// the downloader also waits for that materialization, a reverse edge in host code that the
    /// frame cannot observe; the host contract (<see cref="RunOptions.DownloadCode"/>,
    /// Reentrancy) therefore refuses every selection made under a held turn, which prevents a
    /// possible cycle without proving one. The frame lives exactly as long as the turn, so the
    /// refusal covers the whole load (every downloader call, the parse and the elaboration),
    /// not only a running callback: a later downloader call of the same load can wait for work
    /// an earlier call started, and a frame that ended with its callback would miss that cycle.
    /// Ending the
    /// turn clears its gate reference, so a context captured during the turn and run after it
    /// (a timer, a continuation the downloader left behind) is inert and retains no loader
    /// state. <see cref="Enclosing"/> chains the turns of nested materializations of other
    /// loaders that this context runs, so a cycle through a second tree is caught when it
    /// passes through runs this context started.</para>
    /// </summary>
    private sealed class HeldGateTurn(SemaphoreSlim gate, HeldGateTurn? enclosing)
    {
        private SemaphoreSlim? _gate = gate;

        public HeldGateTurn? Enclosing => enclosing;

        public bool Holds(SemaphoreSlim gate) => ReferenceEquals(Volatile.Read(ref _gate), gate);

        public void End() => Volatile.Write(ref _gate, null);
    }

    private static bool IsInsideHeldGateTurn(SemaphoreSlim gate)
    {
        for (var turn = s_heldGateTurns.Value; turn is not null; turn = turn.Enclosing)
        {
            if (turn.Holds(gate))
                return true;
        }

        return false;
    }

    internal const string ReentrantMaterializationMessage =
        "possible load cycle: an evaluation running in the execution context of a module download selected a branch " +
        "of the same program whose modules are not loaded yet. They cannot load until the load in progress finishes, " +
        "so the selection is refused. An evaluation that does not depend on the download must start outside the " +
        "downloader's execution context or after that load has finished.";

    // The structured failure of a selection refused by the B16 host contract: an ordinary materialization
    // failure carrying one LoadCycle diagnostic, positioned like the region's own load failures
    // (the import site for a family inside a module, otherwise the branch's first load directive).
    private EvalError ReentrantMaterializationRejected()
    {
        LoadElaborationGuard.TryFindFirstUnresolvedLoad(RawBody, out var loadSite);
        var diagnostic = new Diagnostic(ReentrantMaterializationMessage, DiagnosticSeverity.Error, ImportSite ?? loadSite)
        {
            Code = DiagnosticCode.LoadCycle,
        };
        return EvalError.ModuleRegionMaterializationFailed.From([diagnostic]);
    }

    /// <summary>
    /// One evaluation's membership in a <see cref="MaterializationRun"/>. Its leave is performed
    /// by whichever comes first — the evaluation token's registration or the consumer's own
    /// exit from <see cref="MaterializeAsync"/> — and exactly once.
    /// </summary>
    private sealed class MaterializationConsumer(DeferredModuleRegion region, MaterializationRun run)
    {
        private int _left;

        public MaterializationRun Run => run;

        public void Leave()
        {
            if (Interlocked.Exchange(ref _left, 1) == 0)
                region.LeaveRun(run);
        }
    }

    /// <summary>
    /// One underlying materialization shared by every evaluation that selects the region while
    /// it is in flight. <see cref="Consumers"/> counts the evaluations waiting on it (guarded by
    /// the region's run lock); <see cref="Cancellation"/> is cancelled when the last one leaves
    /// before completion, which aborts the wait for the loader's turn or the load in progress.
    /// <see cref="Completion"/> exists before the work starts — the starting consumer runs the
    /// work outside the run lock, possibly inline for its whole duration, so a consumer that
    /// joins meanwhile from another thread always has a completion to wait on (a selection made
    /// from inside the work's own gate turn is rejected before it joins — see
    /// <see cref="HeldGateTurn"/>) — and the
    /// work completes it exactly once, with every outcome, after its own cleanup.
    /// </summary>
    private sealed class MaterializationRun
    {
        public readonly CancellationTokenSource Cancellation = new();

        public int Consumers = 1;

        public bool AbandonRequested;

        public bool CancellationInProgress;

        public bool IsFinished;

        // Continuations run asynchronously: a joiner never resumes on the stack of the thread
        // that completes the work (the starter's, while it runs the work inline).
        public readonly TaskCompletionSource<EvalResult<Algorithm>> Completion =
            new(TaskCreationOptions.RunContinuationsAsynchronously);
    }

    // Joins the region's in-flight run or creates one. It never starts the work, so the lock
    // is held only for the membership update.
    private MaterializationConsumer JoinOrStartRun(out bool starts)
    {
        lock (_runLock)
        {
            var run = _inFlight;
            if (run is not null && !run.AbandonRequested && !run.IsFinished)
            {
                run.Consumers++;
                starts = false;
                return new MaterializationConsumer(this, run);
            }

            run = new MaterializationRun();
            _inFlight = run;
            // A run every consumer abandoned completes with nobody awaiting it; observe its
            // fault so cancellation of unwanted work never surfaces as an unobserved exception.
            ObserveFault(run.Completion.Task);
            starts = true;
            return new MaterializationConsumer(this, run);
        }
    }

    // Runs the work on the starting consumer's stack, outside the run lock.
    private Task<EvalResult<Algorithm>> StartRun(MaterializationRun run)
    {
        var work = RunAsync(run);
        // The starter may leave before the work ends; its fault is also the shared completion's.
        ObserveFault(work);
        return work;
    }

    private static void ObserveFault(Task task)
        => task.ContinueWith(
            static completed => _ = completed.Exception,
            CancellationToken.None,
            TaskContinuationOptions.OnlyOnFaulted | TaskContinuationOptions.ExecuteSynchronously,
            TaskScheduler.Default);

    private void LeaveRun(MaterializationRun run)
    {
        bool abandon;
        var abandonment = 0;
        lock (_runLock)
        {
            if (run.Consumers <= 0)
                throw new InvalidOperationException("Deferred materialization consumer count underflow.");

            run.Consumers--;
            abandon = run.Consumers == 0 && !run.IsFinished && !run.AbandonRequested;
            if (abandon)
            {
                run.AbandonRequested = true;
                run.CancellationInProgress = true;
                // The abandonment transition, counted once; it starts a fresh record.
                abandonment = ++_abandonedRuns;
                _lastAbandonmentFailure = null;
            }
        }

        // Cancel outside the lock: the loader's linked source reacts synchronously.
        if (abandon)
        {
            try
            {
                run.Cancellation.Cancel();
            }
            catch (Exception error)
            {
                // A callback the downloader registered on its token threw. The failure belongs to
                // the abandoned run: it must not replace the leaving consumer's cancellation, nor
                // escape into the host's Cancel() when this leave runs inside a token callback.
                // Only a bounded summary is kept, and only while this is still the most recent
                // abandonment: the record never retains the exception graph or the run.
                var summary = AbandonmentFailureSummary.Of(error);
                lock (_runLock)
                {
                    if (_abandonedRuns == abandonment)
                        _lastAbandonmentFailure = summary;
                }
            }
            finally
            {
                lock (_runLock)
                {
                    run.CancellationInProgress = false;
                    if (run.IsFinished)
                        run.Cancellation.Dispose();
                }
            }
        }
    }

    // The work. It completes the run's shared completion exactly once, with every outcome,
    // after its own cleanup (RunCoreAsync's finally) has finished the run and cleared it from
    // the region, so a joiner observes the same ordering the work's own task gives the starter.
    private async Task<EvalResult<Algorithm>> RunAsync(MaterializationRun run)
    {
        try
        {
            var result = await RunCoreAsync(run).ConfigureAwait(false);
            run.Completion.TrySetResult(result);
            return result;
        }
        catch (OperationCanceledException error)
        {
            run.Completion.TrySetCanceled(error.CancellationToken);
            throw;
        }
        catch (Exception error)
        {
            run.Completion.TrySetException(error);
            throw;
        }
    }

    private async Task<EvalResult<Algorithm>> RunCoreAsync(MaterializationRun run)
    {
        using var linkedCancellation = CancellationTokenSource.CreateLinkedTokenSource(
            Loader.SourceProcessingCancellationToken, run.Cancellation.Token);
        var cancellationToken = linkedCancellation.Token;
        try
        {
            var gate = Loader.MaterializationGate;
            await gate.WaitAsync(cancellationToken).ConfigureAwait(false);
            // B16: the turn is visible to the downloader this work calls and to what it starts in
            // its flowed context, and to nothing else (the write is scoped to this async method).
            var turn = new HeldGateTurn(gate, s_heldGateTurns.Value);
            s_heldGateTurns.Value = turn;
            try
            {
                if (TryGetMaterialized(out var ready))
                    return EvalResult<Algorithm>.Ok(ready);

                Interlocked.Increment(ref _materializationAttempts);
                // One materialization is one operation with its own bounded diagnostic list —
                // the one this evaluation's error reports; nothing accumulates across attempts.
                var diagnostics = Loader.CreateDiagnosticBag();
                // The attempt's own splice ledger: released below, under the gate, unless the
                // attempt publishes (see MaterializeAsync, Accounting of an attempt).
                var attemptLedger = Loader.CreateMaterializationLedger();
                var published = false;
                try
                {
                    var loaded = await Loader.LoadDeferredRegionAsync(this, diagnostics, attemptLedger, cancellationToken).ConfigureAwait(false);
                    if (!diagnostics.HasReportedErrors)
                    {
                        cancellationToken.ThrowIfCancellationRequested();
                        var observations = Loader.TraversalObservations;
                        // The program's loaded modules are ONE unit each (Q-32 I-U): the body's loads
                        // receive the declarations earlier operations elaborated (ModuleUnitRegistry).
                        var modules = Loader.ModuleUnits.BeginOperation();
                        // Name resolution, then automatic parameter forwarding, exactly as the eager
                        // pipeline runs them (Q-04: forwarding never re-selects a binding). Every
                        // demand-time pass starts from the import site the region recorded: a
                        // diagnostic raised against module content — which carries no source
                        // location — is positioned at the site the current document wrote.
                        var exposed = CompileLoadedBody(loaded, diagnostics, observations, modules, out var continuation, cancellationToken);
                        if (exposed is not null)
                        {
                            lock (_runLock)
                            {
                                cancellationToken.ThrowIfCancellationRequested();
                                if (run.AbandonRequested)
                                    throw new OperationCanceledException(cancellationToken);

                                Volatile.Write(ref _materialized, exposed);
                                published = true;
                                run.IsFinished = true;
                                modules.Publish(continuation);
                            }
                            return EvalResult<Algorithm>.Ok(exposed);
                        }
                    }

                    // The evaluation's error keeps a read-only snapshot of the bounded list.
                    return EvalError.ModuleRegionMaterializationFailed.From(Array.AsReadOnly(diagnostics.ToArray()));
                }
                finally
                {
                    // An attempt that published nothing added nothing to the program, whatever
                    // the reason: release its own splices (exactly once; a release during the
                    // load on cancellation already zeroed the ledger). Downloads stay charged.
                    if (!published)
                        Loader.ReleaseUnpublishedSplices(attemptLedger);
                }
            }
            finally
            {
                // End the turn BEFORE releasing the gate, so no context that captured it can
                // be rejected once the gate is free.
                turn.End();
                s_heldGateTurns.Value = turn.Enclosing;
                gate.Release();
            }
        }
        finally
        {
            lock (_runLock)
            {
                run.IsFinished = true;
                if (ReferenceEquals(_inFlight, run))
                    _inFlight = null;
                if (!run.CancellationInProgress)
                    run.Cancellation.Dispose();
            }
        }
    }

    private Algorithm? CompileLoadedBody(Algorithm loaded, DiagnosticBag diagnostics, FrontEndTraversalObservations? observations,
        ModuleUnits modules, out StaticStructureOperation.Continuation? continuation, CancellationToken cancellationToken)
    {
        continuation = null;
        try
        {
            var structural = Structure ?? throw new InvalidOperationException("Deferred compilation requires a shared structural context.");
            var completed = structural.Registry.StructuralContinuation
                ?? throw new InvalidOperationException("A deferred structural unit requires completed eager publications.");
            var limits = StaticStructureAdmission.Measure(loaded, completed.Prelude, Loader.ProcessingLimits, cancellationToken: cancellationToken).Limits;
            var operation = completed.Materialize(structural.Declaring, loaded, structural.Pattern, limits, cancellationToken);
            var detection = new ParameterDetector.DeferredBranchContext(operation.LookupLevel(structural.Declaring),
                new HashSet<string>(structural.Pattern.BoundNamesExpandingSharedNodesOnce(), StringComparer.Ordinal), structural.BranchName, structural.CapturedParameters);
            var detected = ParameterDetector.ElaborateDeferredBranch(loaded, detection, diagnostics, observations, ImportSite, modules, structural.Pattern);
            cancellationToken.ThrowIfCancellationRequested();
            if (diagnostics.HasReported(DiagnosticCode.SelfDependentInferredParameters))
            {
                // A1 recovery (F4), as in the eager pipeline: the branch fails unpublished, and only
                // the collision rule runs, over the detected body.
                ParameterPropertyCollisionValidator.ValidateAfterSelfDependentInference(
                    detected, diagnostics, Validation, programRoot: null, ImportSite);
                return null;
            }
            var resolved = ImplicitArgumentResolver.ElaborateStructuralDeferredBranch(detected, structural, operation,
                diagnostics, observations, ImportSite, modules);
            cancellationToken.ThrowIfCancellationRequested();
            if (diagnostics.HasReported(DiagnosticCode.SelfDependentInferredParameters))
            {
                // B3-5★: a refused signature selection is the same family, with the same recovery: the resolver returned
                // the detected body unrewritten and unpublished, and only the collision rule runs over it.
                ParameterPropertyCollisionValidator.ValidateAfterSelfDependentInference(
                    resolved, diagnostics, Validation, programRoot: null, ImportSite);
                return null;
            }
            if (diagnostics.HasReportedErrors) return null;
            new ParameterPropertyCollisionValidator(diagnostics, Validation, importSite: ImportSite) { CancellationToken = cancellationToken }
                .VisitAlgorithm(resolved);
            OpenProviderValidator.Validate(resolved, diagnostics, Exposure!.Scope.PropertyScope, ImportSite, cancellationToken: cancellationToken);
            InferredParameterOutputValidator.ValidateDeferredBody(resolved, diagnostics, ImportSite, cancellationToken);
            if (diagnostics.HasReportedErrors) return null;
            var exposed = PropertyExposureResolver.ElaborateDeferredBranch(resolved, Exposure!, observations, modules, cancellationToken);
            cancellationToken.ThrowIfCancellationRequested();
            continuation = operation.Freeze(cancellationToken);
            return exposed;
        }
        catch (StaticQueryLimitExceededException error)
        {
            diagnostics.Add(StaticStructureAdmission.Rejection(error));
            return null;
        }
        catch (FrontEndStackExhaustedException)
        {
            // A pass's per-level stack probe fired (FrontEndStack): this compile runs on whatever
            // stack evaluation had already used when the branch was selected. Nothing was
            // published (the operation is frozen only on success), so the region stays
            // retryable — the same tree compiles on a run with more stack.
            diagnostics.Add(SourceProcessingDiagnostics.ModuleElaborationStackExhausted(ModuleLoader.MaxTraversalDepth));
            return null;
        }
    }

    // ── Routing helpers (stateless) ─────────────────────────────────────────

    /// <summary>
    /// Whether evaluating <paramref name="expr"/> can reach a deferred module region — the
    /// ONE fact that routes a run to the async evaluation family (materializing a selected
    /// branch awaits the module downloader) and makes the synchronous entry points reject
    /// the tree. Answered from the tree itself: an iterative walk over the structural
    /// children (the same enumeration the structural preflight uses, host copies and
    /// enclosing captures included) that stops at the first placeholder body it meets. There
    /// is no root mark to keep in step with copies: a <c>with</c> copy of the root, or of
    /// any subtree, carries its placeholders and their regions with it.
    /// </summary>
    internal static bool RequiresAsyncEvaluation(Expr expr)
    {
        var pending = new Stack<object>();
        var visited = new HashSet<object>(ReferenceEqualityComparer.Instance);
        pending.Push(expr);
        while (pending.TryPop(out var node))
        {
            if (!visited.Add(node))
                continue;

            if (node is Algorithm { DeferredRegion: not null })
                return true;

            for (var index = 0; AstStructuralPreflight.TryGetChild(node, index, out var child); index++)
                pending.Push(child);
        }

        return false;
    }

    internal static InvalidOperationException SynchronousSelectionNotSupported()
        => new(
            "A conditional branch whose module dependencies load on demand was selected on a synchronous evaluation " +
            "path before it was materialized. Deferred module regions are materialized by awaiting the module " +
            "downloader, which a synchronous evaluation entry point cannot do; evaluate the program through " +
            "Evaluator.RunAsync or an async KatLangEngine entry point.");
}
