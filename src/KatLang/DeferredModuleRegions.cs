using System.Diagnostics.CodeAnalysis;
using System.Runtime.CompilerServices;

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
/// <para>Contexts are recorded per REGION, never per shared node: every pass that reaches a
/// deferred branch registers a fresh body object for its own output tree, so a branch body
/// shared between two host regions gets two independent records and can never inherit the
/// materialization of whichever region ran first.</para>
///
/// <para>Lean has no counterpart: its input model is an already-elaborated tree with no
/// external modules and no demand timing. Once materialized, the selected branch is the very
/// tree eager elaboration would have produced, so core semantics are unchanged — only host
/// dependency materialization (and the timing of module-load and demand-time elaboration
/// diagnostics) moves to the selection boundary.</para>
/// </summary>
internal sealed class DeferredModuleRegion
{
    private readonly object _runLock = new();
    private Algorithm? _materialized;
    private int _materializationAttempts;
    private MaterializationRun? _inFlight;

    internal DeferredModuleRegion(
        ModuleLoader loader,
        Algorithm rawBody,
        ModuleLoader.LoadContext context,
        int depth,
        int nestedTraversalBase)
    {
        Loader = loader;
        RawBody = rawBody;
        Context = context;
        Depth = depth;
        NestedTraversalBase = nestedTraversalBase;
    }

    private DeferredModuleRegion(DeferredModuleRegion source)
    {
        Loader = source.Loader;
        RawBody = source.RawBody;
        Context = source.Context;
        Depth = source.Depth;
        NestedTraversalBase = source.NestedTraversalBase;
        Detection = source.Detection;
        Resolution = source.Resolution;
        Exposure = source.Exposure;
    }

    /// <summary>The loader that deferred the region: its cache, budget, policy, and downloader.</summary>
    internal ModuleLoader Loader { get; }

    /// <summary>The branch body exactly as the loader found it — unelaborated, with its load directives.</summary>
    internal Algorithm RawBody { get; }

    /// <summary>The load context the family was reached under; the body inherits it, exactly as eager elaboration would apply it.</summary>
    internal ModuleLoader.LoadContext Context { get; }

    /// <summary>The body's counted traversal depth within its tree, so its loads are judged at the depth eager elaboration would have used.</summary>
    internal int Depth { get; }

    /// <summary>The live traversal base at deferral (non-zero when the family sits inside a loaded module).</summary>
    internal int NestedTraversalBase { get; }

    internal ParameterDetector.DeferredBranchContext? Detection { get; private init; }

    internal ImplicitArgumentResolver.DeferredBranchContext? Resolution { get; private init; }

    internal PropertyExposureResolver.DeferredBranchContext? Exposure { get; private init; }

    internal DeferredModuleRegion WithDetection(ParameterDetector.DeferredBranchContext detection)
        => new(this) { Detection = detection };

    internal DeferredModuleRegion WithResolution(ImplicitArgumentResolver.DeferredBranchContext resolution)
        => new(this) { Resolution = resolution };

    internal DeferredModuleRegion WithExposure(PropertyExposureResolver.DeferredBranchContext exposure)
        => new(this) { Exposure = exposure };

    /// <summary>Completed materializations plus failed attempts; test-observable, never a decision input.</summary>
    internal int MaterializationAttempts => Volatile.Read(ref _materializationAttempts);

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
    /// </summary>
    internal async ValueTask<EvalResult<Algorithm>> MaterializeAsync(CancellationToken evaluationCancellationToken)
    {
        if (TryGetMaterialized(out var ready))
            return EvalResult<Algorithm>.Ok(ready);

        if (Detection is null || Resolution is null || Exposure is null)
        {
            throw new InvalidOperationException(
                "Internal error: a deferred module region reached evaluation without its complete elaboration context. " +
                "The front-end pipeline registers every deferred branch through parameter detection, implicit-argument " +
                "resolution, and exposure resolution before a tree is evaluated.");
        }

        Loader.SourceProcessingCancellationToken.ThrowIfCancellationRequested();
        evaluationCancellationToken.ThrowIfCancellationRequested();

        var run = JoinOrStartRun();
        try
        {
            return await run.Completion.WaitAsync(evaluationCancellationToken).ConfigureAwait(false);
        }
        catch (OperationCanceledException)
        {
            Loader.SourceProcessingCancellationToken.ThrowIfCancellationRequested();
            evaluationCancellationToken.ThrowIfCancellationRequested();
            throw;
        }
        finally
        {
            LeaveRun(run);
        }
    }

    /// <summary>
    /// One underlying materialization shared by every evaluation that selects the region while
    /// it is in flight. <see cref="Consumers"/> counts the evaluations waiting on it (guarded by
    /// the region's run lock); <see cref="Cancellation"/> is cancelled when the last one leaves
    /// before completion, which aborts the wait for the loader's turn or the load in progress.
    /// </summary>
    private sealed class MaterializationRun
    {
        public readonly CancellationTokenSource Cancellation = new();

        public int Consumers = 1;

        public bool AbandonRequested;

        public bool CancellationInProgress;

        public bool IsFinished;

        public Task<EvalResult<Algorithm>> Completion = null!;
    }

    private MaterializationRun JoinOrStartRun()
    {
        lock (_runLock)
        {
            var run = _inFlight;
            if (run is not null && !run.AbandonRequested && !run.IsFinished)
            {
                run.Consumers++;
                return run;
            }

            run = new MaterializationRun();
            _inFlight = run;
            run.Completion = RunAsync(run);
            // A run every consumer abandoned completes with nobody awaiting it; observe its
            // fault so cancellation of unwanted work never surfaces as an unobserved exception.
            run.Completion.ContinueWith(
                static completed => _ = completed.Exception,
                CancellationToken.None,
                TaskContinuationOptions.OnlyOnFaulted | TaskContinuationOptions.ExecuteSynchronously,
                TaskScheduler.Default);
            return run;
        }
    }

    private void LeaveRun(MaterializationRun run)
    {
        bool abandon;
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
            }
        }

        // Cancel outside the lock: the loader's linked source reacts synchronously.
        if (abandon)
        {
            try
            {
                run.Cancellation.Cancel();
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

    private async Task<EvalResult<Algorithm>> RunAsync(MaterializationRun run)
    {
        using var linkedCancellation = CancellationTokenSource.CreateLinkedTokenSource(
            Loader.SourceProcessingCancellationToken, run.Cancellation.Token);
        var cancellationToken = linkedCancellation.Token;
        try
        {
            var gate = Loader.MaterializationGate;
            await gate.WaitAsync(cancellationToken).ConfigureAwait(false);
            try
            {
                if (TryGetMaterialized(out var ready))
                    return EvalResult<Algorithm>.Ok(ready);

                Interlocked.Increment(ref _materializationAttempts);
                var diagnostics = new List<Diagnostic>();
                var loaded = await Loader.LoadDeferredRegionAsync(this, diagnostics, cancellationToken).ConfigureAwait(false);
                if (!HasErrors(diagnostics))
                {
                    cancellationToken.ThrowIfCancellationRequested();
                    var observations = Loader.TraversalObservations;
                    var detected = ParameterDetector.ElaborateDeferredBranch(loaded, Detection!, diagnostics, observations);
                    cancellationToken.ThrowIfCancellationRequested();
                    var resolved = ImplicitArgumentResolver.ElaborateDeferredBranch(detected, Resolution!, diagnostics, observations);
                    cancellationToken.ThrowIfCancellationRequested();
                    if (!HasErrors(diagnostics))
                    {
                        var exposed = PropertyExposureResolver.ElaborateDeferredBranch(resolved, Exposure!, observations);
                        lock (_runLock)
                        {
                            cancellationToken.ThrowIfCancellationRequested();
                            if (run.AbandonRequested)
                                throw new OperationCanceledException(cancellationToken);

                            Volatile.Write(ref _materialized, exposed);
                            run.IsFinished = true;
                        }
                        return EvalResult<Algorithm>.Ok(exposed);
                    }
                }

                return EvalError.ModuleRegionMaterializationFailed.From(diagnostics);
            }
            finally
            {
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

    private static bool HasErrors(List<Diagnostic> diagnostics)
    {
        foreach (var diagnostic in diagnostics)
        {
            if (diagnostic.Severity == DiagnosticSeverity.Error)
                return true;
        }

        return false;
    }
}

/// <summary>
/// The registry of deferred module regions, keyed by the REFERENCE identity of the branch
/// body object that stands in the elaborated tree. Per-node metadata rather than a traversal
/// memo (it is weak, so it retains nothing beyond the trees it annotates, and it is never
/// consulted as a cache of traversal work); the same discipline as
/// <see cref="FinalPropertyExposure"/>. Keys are unique per region by construction: the
/// loader registers a fresh placeholder per branch occurrence, and each later pass registers
/// its own output body, so two regions sharing one raw body never share a record.
/// </summary>
internal static class DeferredModuleRegions
{
    private static readonly ConditionalWeakTable<Algorithm, DeferredModuleRegion> Regions = new();

    private static readonly ConditionalWeakTable<Algorithm, object> RootsRequiringAsyncEvaluation = new();

    private static readonly object RootMarker = new();

    internal static void Register(Algorithm body, DeferredModuleRegion region)
        => Regions.AddOrUpdate(body, region);

    internal static bool TryGet(Algorithm body, [NotNullWhen(true)] out DeferredModuleRegion? region)
        => Regions.TryGetValue(body, out region);

    internal static bool IsDeferred(Algorithm body)
        => Regions.TryGetValue(body, out _);

    /// <summary>
    /// Marks an elaborated root that contains deferred regions: evaluating it requires the
    /// async evaluation family, because materialization awaits the module downloader. The
    /// front-end pipeline marks every such root; a manually assembled pipeline marks its
    /// root the same way.
    /// </summary>
    internal static void MarkRootRequiresAsyncEvaluation(Algorithm root)
        => RootsRequiringAsyncEvaluation.AddOrUpdate(root, RootMarker);

    internal static bool RequiresAsyncEvaluation(Expr expr)
    {
        var pending = new Stack<object>();
        var visited = new HashSet<object>(ReferenceEqualityComparer.Instance);
        pending.Push(expr);
        while (pending.TryPop(out var node))
        {
            if (!visited.Add(node))
                continue;

            if (node is Algorithm algorithm
                && (RootsRequiringAsyncEvaluation.TryGetValue(algorithm, out _) || IsDeferred(algorithm)))
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
