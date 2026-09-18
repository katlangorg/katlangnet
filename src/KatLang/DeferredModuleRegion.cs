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
/// facts plus the pass's own context, see <see cref="WithDetection"/>,
/// <see cref="WithResolution"/>, and <see cref="WithExposure"/> — on the output view it
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
    private ParameterPropertyCollisionValidator.ParameterBindings? _validation;

    internal DeferredModuleRegion(
        ModuleLoader loader,
        Algorithm rawBody,
        ModuleLoader.LoadContext context,
        int depth,
        int nestedTraversalBase,
        SourceSpan? importSite)
    {
        if (rawBody.DeferredRegion is not null)
            throw new ArgumentException("A deferred region's raw body is unelaborated source structure and carries no region.", nameof(rawBody));

        Loader = loader;
        RawBody = rawBody;
        Context = context;
        Depth = depth;
        NestedTraversalBase = nestedTraversalBase;
        ImportSite = importSite;
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
        Detection = source.Detection;
        Resolution = source.Resolution;
        _validation = source._validation;
        Exposure = source.Exposure;
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

    /// <summary>Installed by parameter detection on its output view of the placeholder (replaced when ownership completion re-detects).</summary>
    internal ParameterDetector.DeferredBranchContext? Detection { get; private init; }

    /// <summary>Installed by implicit-argument resolution on its output view (replaced by the signature-preserving re-resolution).</summary>
    internal ImplicitArgumentResolver.DeferredBranchContext? Resolution { get; private init; }

    /// <summary>Installed by property-exposure resolution on its output view — the last eager pass, so the tree's final region carries every context.</summary>
    internal PropertyExposureResolver.DeferredBranchContext? Exposure { get; private init; }

    /// <summary>Recorded by declaration validation (see <see cref="RecordValidation"/>); carried by every later fork.</summary>
    internal ParameterPropertyCollisionValidator.ParameterBindings? Validation => _validation;

    internal DeferredModuleRegion WithDetection(ParameterDetector.DeferredBranchContext detection)
        => new(this) { Detection = detection };

    internal DeferredModuleRegion WithResolution(ImplicitArgumentResolver.DeferredBranchContext resolution)
        => new(this) { Resolution = resolution };

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

        if (Detection is null || Resolution is null || Validation is null || Exposure is null)
        {
            throw new InvalidOperationException(
                "Internal error: a deferred module region reached evaluation without its complete elaboration context. " +
                "The front-end pipeline carries every deferred branch through parameter detection, implicit-argument " +
                "resolution, declaration validation, and exposure resolution before a tree is evaluated.");
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
                    var parameterDiagnosticStart = diagnostics.Count;
                    var origins = new ImplicitArgumentResolver.ResolutionOrigins();
                    // Every demand-time pass starts from the import site the region recorded:
                    // a diagnostic raised against module content — which carries no source
                    // location — is positioned at the site the current document wrote.
                    var detected = ParameterDetector.ElaborateDeferredBranch(
                        loaded, Detection!, diagnostics, observations, origins.Grace, ImportSite);
                    cancellationToken.ThrowIfCancellationRequested();
                    var resolved = ImplicitArgumentResolver.ElaborateDeferredBranch(
                        detected, Resolution!, diagnostics, observations, origins, importSite: ImportSite);
                    if (origins.HasLiftedParameters)
                    {
                        var completed = ParameterDetector.CompleteOwnership(
                            resolved, origins, branchContext: Detection!, observations: observations, importSite: ImportSite);
                        if (completed.Changed)
                        {
                            diagnostics.RemoveRange(parameterDiagnosticStart, diagnostics.Count - parameterDiagnosticStart);
                            diagnostics.AddRange(completed.Diagnostics);
                            resolved = ImplicitArgumentResolver.ElaborateDeferredBranch(
                                completed.Root, Resolution!, diagnostics, observations, preserveSignatures: true, importSite: ImportSite);
                        }
                    }
                    cancellationToken.ThrowIfCancellationRequested();
                    if (!HasErrors(diagnostics))
                    {
                        new ParameterPropertyCollisionValidator(diagnostics, Validation, importSite: ImportSite).VisitAlgorithm(resolved);
                        OpenProviderValidator.Validate(resolved, diagnostics, Exposure!.Scope.PropertyScope, ImportSite);
                    }
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
