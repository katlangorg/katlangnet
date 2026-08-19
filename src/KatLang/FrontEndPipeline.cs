namespace KatLang;

/// <summary>
/// Explicit KatLang front-end boundary.
/// Starts from raw syntax and produces an elaborated program ready for
/// evaluator-facing and semantic-model consumers.
/// </summary>
internal static class FrontEndPipeline
{
    internal static FrontEndResult Process(string source)
    {
        var budget = new SourceProcessingBudget(null);
        if (TryRejectMainSource(source, budget, out var rejected))
            return rejected;

        return ProcessWithoutModuleElaboration(Parser.ParseSyntax(source), hostOperations: null, CancellationToken.None);
    }

    /// <summary>
    /// Synchronous options-configured front end. Module elaboration is ASYNC-ONLY
    /// (obtaining source text for <c>load</c> awaits <see cref="RunOptions.DownloadCode"/>),
    /// so a downloader-configured options object is rejected here before any parsing —
    /// there is no synchronous module-fetching pipeline to fall back to, and no blocking
    /// bridge is ever taken. Downloader-less options keep full synchronous processing:
    /// parsing and every elaboration pass are CPU work, and <c>load</c> syntax without a
    /// downloader keeps its established unavailability diagnostic.
    /// </summary>
    /// <exception cref="InvalidOperationException">
    /// <see cref="RunOptions.DownloadCode"/> is configured; use the asynchronous pipeline
    /// (<see cref="ProcessAsync"/> via <see cref="KatLangEngine.RunAsync"/> or
    /// <see cref="Parser.ParseAsync"/>).
    /// </exception>
    internal static FrontEndResult Process(string source, RunOptions? options)
    {
        ThrowIfSynchronousEntryWithDownloader(options);

        var cancellationToken = options?.SourceProcessingCancellationToken ?? CancellationToken.None;
        cancellationToken.ThrowIfCancellationRequested();

        var budget = new SourceProcessingBudget(options?.SourceProcessingLimits);
        if (TryRejectMainSource(source, budget, out var rejected))
            return rejected;

        var syntaxResult = Parser.ParseSyntax(source);
        cancellationToken.ThrowIfCancellationRequested();

        return ProcessWithoutModuleElaboration(syntaxResult, options?.HostOperations, cancellationToken);
    }

    /// <summary>
    /// Asynchronous options-configured front end — the canonical path when
    /// <see cref="RunOptions.DownloadCode"/> is configured. Parsing, parameter detection,
    /// implicit-argument resolution, and exposure resolution remain synchronous CPU work;
    /// only module acquisition awaits, inside <see cref="ModuleLoader.ElaborateAsync"/>.
    /// With no downloader configured (or a downloader whose ValueTasks complete
    /// synchronously) the returned task completes synchronously on the calling thread —
    /// no work is scheduled elsewhere and nothing yields artificially.
    /// </summary>
    internal static async ValueTask<FrontEndResult> ProcessAsync(string source, RunOptions? options)
    {
        // MIRROR OF Process(string, RunOptions?) — keep in lock-step; only module
        // elaboration is awaited.
        var cancellationToken = options?.SourceProcessingCancellationToken ?? CancellationToken.None;
        cancellationToken.ThrowIfCancellationRequested();

        var budget = new SourceProcessingBudget(options?.SourceProcessingLimits);
        if (TryRejectMainSource(source, budget, out var rejected))
            return rejected;

        var syntaxResult = Parser.ParseSyntax(source);
        cancellationToken.ThrowIfCancellationRequested();

        if (options?.DownloadCode is not null)
            return await ProcessWithModuleElaborationAsync(
                syntaxResult,
                options.DownloadCode,
                options.AllowedHosts,
                budget,
                options.HostOperations,
                cancellationToken).ConfigureAwait(false);

        return ProcessWithoutModuleElaboration(syntaxResult, options?.HostOperations, cancellationToken);
    }

    /// <summary>
    /// The one enforcement point for the async-only source-loading contract on
    /// synchronous entry paths (<see cref="KatLangEngine.Run"/>,
    /// <see cref="Parser.Parse(string, RunOptions?)"/>): module downloading awaits, so a
    /// synchronous entry cannot honor a downloader-configured options object and fails
    /// fast instead of blocking a thread or silently ignoring the configuration.
    /// </summary>
    private static void ThrowIfSynchronousEntryWithDownloader(RunOptions? options)
    {
        if (options?.DownloadCode is not null)
        {
            throw new InvalidOperationException(
                "RunOptions.DownloadCode is configured, but module loading is asynchronous; use " +
                "KatLangEngine.RunAsync (or an async convenience entry point) or Parser.ParseAsync, " +
                "or omit the downloader for source without load directives.");
        }
    }

    /// <summary>
    /// Enforces the configured per-source length ceiling on the MAIN program before parsing and
    /// reserves it against the run-wide aggregate. A rejected source produces one structured
    /// <see cref="SourceProcessingDiagnostics.SourceLengthExceeded"/> diagnostic and no parse.
    /// </summary>
    private static bool TryRejectMainSource(string source, SourceProcessingBudget budget, out FrontEndResult rejected)
    {
        if (!budget.SourceLengthWithinLimit(source.Length))
        {
            rejected = new FrontEndResult(
                new Algorithm.User(null, [], [], [], []),
                [SourceProcessingDiagnostics.SourceLengthExceeded(source.Length, budget.MaxSourceLength)]);
            return true;
        }

        // Reserve the main program against the run-wide aggregate before any module is loaded, so
        // modules are charged on top of it. By default the per-source ceiling never exceeds the
        // aggregate ceiling, so this fits; a caller that configured the aggregate below its own
        // program source is rejected here rather than silently proceeding.
        if (!budget.TryReserveAggregate(source.Length))
        {
            rejected = new FrontEndResult(
                new Algorithm.User(null, [], [], [], []),
                [SourceProcessingDiagnostics.AggregateSourceLengthExceededByProgram(source.Length, budget.MaxAggregateSourceLength)]);
            return true;
        }

        rejected = null!;
        return false;
    }

    private static FrontEndResult ProcessWithoutModuleElaboration(
        SyntaxParseResult syntaxResult,
        HostOperations? hostOperations,
        CancellationToken cancellationToken)
    {
        var diagnostics = new List<Diagnostic>(syntaxResult.Diagnostics);
        var loadDiagnostics = LoadElaborationGuard.CreateUnavailableDiagnostics(syntaxResult.SyntaxRoot);

        if (loadDiagnostics.Count > 0)
        {
            diagnostics.AddRange(loadDiagnostics);
            return new FrontEndResult(syntaxResult.SyntaxRoot, diagnostics);
        }

        return FinalizeElaboration(
            syntaxResult.SyntaxRoot, diagnostics, hostOperations: hostOperations, cancellationToken: cancellationToken);
    }

    private static async ValueTask<FrontEndResult> ProcessWithModuleElaborationAsync(
        SyntaxParseResult syntaxResult,
        Func<string, CancellationToken, ValueTask<string>> downloadCode,
        IEnumerable<string>? allowedHosts,
        SourceProcessingBudget budget,
        HostOperations? hostOperations,
        CancellationToken cancellationToken)
    {
        var diagnostics = new List<Diagnostic>(syntaxResult.Diagnostics);

        var loadDiagnosticStart = diagnostics.Count;
        var loader = new ModuleLoader(
            diagnostics,
            downloadCode,
            allowedHosts,
            budget,
            cancellationToken);
        var loadElaboratedRoot = await loader.ElaborateAsync(syntaxResult.SyntaxRoot).ConfigureAwait(false);
        cancellationToken.ThrowIfCancellationRequested();
        var loadDiagnosticsEnd = diagnostics.Count;

        // Module elaboration splices independently parsed module trees (each already
        // structurally checked by ParseSyntax) into the host tree, so the COMPOSED root
        // can be deeper than any single parse. Re-check it at the raw-syntax cap before
        // the recursive load-invariant walk below; a rejected composition returns the
        // same placeholder-root convention ParseSyntax uses, so no downstream consumer
        // ever walks the unsafe tree. (FinalizeElaboration then applies the lower
        // elaboration gate shared with the non-module path.)
        if (AstStructuralPreflight.Check(
                loadElaboratedRoot,
                AstStructuralPreflight.RawSyntaxMaxAstDepth,
                AstConsumerProfile.FullyRecursive) is { } structuralRejection)
        {
            diagnostics.Add(AstStructuralPreflight.ToParseDiagnostic(
                structuralRejection, AstStructuralPreflight.RawSyntaxMaxAstDepth));
            return new FrontEndResult(new Algorithm.User(null, [], [], [], []), diagnostics);
        }

        if (LoadElaborationGuard.TryFindFirstUnresolvedLoad(loadElaboratedRoot, out _))
        {
            diagnostics.Add(LoadElaborationGuard.CreatePostElaborationInvariantDiagnostic(loadElaboratedRoot));
            return new FrontEndResult(loadElaboratedRoot, diagnostics);
        }

        return FinalizeElaboration(
            loadElaboratedRoot,
            diagnostics,
            canEvaluateAfterLoadErrors:
                !syntaxResult.HasErrors &&
                !loader.HasSourceProcessingErrors &&
                diagnostics
                    .Skip(loadDiagnosticStart)
                    .Take(loadDiagnosticsEnd - loadDiagnosticStart)
                    .Any(static d => d.Severity == DiagnosticSeverity.Error),
            hostOperations: hostOperations,
            cancellationToken: cancellationToken);
    }

    private static FrontEndResult FinalizeElaboration(
        Algorithm loadElaboratedRoot,
        List<Diagnostic> diagnostics,
        bool canEvaluateAfterLoadErrors = false,
        HostOperations? hostOperations = null,
        CancellationToken cancellationToken = default)
    {
        cancellationToken.ThrowIfCancellationRequested();

        // The elaboration passes below (parameter detection's rewriting walk,
        // implicit-argument and exposure resolution) recurse with evaluation-class
        // frame sizes — a ~500-626-node composed tree overflows a 1 MiB thread inside
        // ParameterDetector.RewriteParams — so trees between the raw-syntax cap and
        // the evaluation ceiling are rejected HERE, on both the module and non-module
        // paths, with one structured diagnostic instead of being walked at
        // machine-dependent risk. Anything this gate passes is also within the
        // evaluator's own structural ceiling. This is the pipeline's ONE common gate:
        // the passes below run through their prevalidated cores, so the modest
        // depth growth elaboration itself adds (parameter lifting wraps calls) is
        // absorbed by the ceiling's measured ≥2x margin rather than re-gated
        // mid-pipeline.
        if (AstStructuralPreflight.Check(
                loadElaboratedRoot,
                EvaluationLimits.MaxSupportedAstDepth,
                AstConsumerProfile.FullyRecursive) is { } elaborationRejection)
        {
            diagnostics.Add(AstStructuralPreflight.ToParseDiagnostic(
                elaborationRejection, EvaluationLimits.MaxSupportedAstDepth));
            return new FrontEndResult(new Algorithm.User(null, [], [], [], []), diagnostics);
        }

        // Host-operation names resolve during parameter detection (through the
        // configuration's extended semantic prelude), so referencing one never turns
        // it into an implicit parameter — the front-end half of the same name-level
        // agreement the built-in Math module relies on.
        var (parameterizedRoot, parameterDiagnostics) = ParameterDetector.DetectPrevalidated(loadElaboratedRoot, hostOperations);
        diagnostics.AddRange(parameterDiagnostics);

        cancellationToken.ThrowIfCancellationRequested();
        var implicitResolvedRoot = ImplicitArgumentResolver.ResolvePrevalidated(parameterizedRoot);
        cancellationToken.ThrowIfCancellationRequested();
        var propertyExposedRoot = PropertyExposureResolver.Resolve(implicitResolvedRoot);
        cancellationToken.ThrowIfCancellationRequested();
        return new FrontEndResult(propertyExposedRoot, diagnostics, canEvaluateAfterLoadErrors);
    }
}

/// <summary>
/// Raw syntax result produced directly by the recursive-descent parser.
/// No front-end elaboration passes have run yet.
/// </summary>
internal sealed record SyntaxParseResult(Algorithm Root, IReadOnlyList<Diagnostic> Diagnostics)
{
    public Algorithm SyntaxRoot => Root;

    public bool HasErrors => Diagnostics.Any(d => d.Severity == DiagnosticSeverity.Error);
}

/// <summary>
/// Internal front-end result after load elaboration, parameter detection,
/// implicit argument resolution, and property exposure analysis.
/// </summary>
internal sealed record FrontEndResult(
    Algorithm ElaboratedRoot,
    IReadOnlyList<Diagnostic> Diagnostics,
    bool CanEvaluateAfterLoadErrors = false)
{
    public bool HasErrors => Diagnostics.Any(d => d.Severity == DiagnosticSeverity.Error);

    public ParseResult ToParseResult() => new(ElaboratedRoot, Diagnostics);
}
