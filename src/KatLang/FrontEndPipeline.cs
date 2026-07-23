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

        return ProcessWithoutModuleElaboration(Parser.ParseSyntax(source));
    }

    internal static FrontEndResult Process(
        string source,
        Func<string, string>? downloadCode,
        IEnumerable<string>? allowedHosts = null)
    {
        var budget = new SourceProcessingBudget(null);
        if (TryRejectMainSource(source, budget, out var rejected))
            return rejected;

        return ProcessWithModuleElaboration(Parser.ParseSyntax(source), downloadCode, allowedHosts, budget);
    }

    internal static FrontEndResult Process(string source, RunOptions? options)
    {
        var budget = new SourceProcessingBudget(options?.SourceProcessingLimits);
        if (TryRejectMainSource(source, budget, out var rejected))
            return rejected;

        if (options?.DownloadCode is not null)
            return ProcessWithModuleElaboration(
                Parser.ParseSyntax(source), options.DownloadCode, options.AllowedHosts, budget);

        return ProcessWithoutModuleElaboration(Parser.ParseSyntax(source));
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

    private static FrontEndResult ProcessWithoutModuleElaboration(SyntaxParseResult syntaxResult)
    {
        var diagnostics = new List<Diagnostic>(syntaxResult.Diagnostics);
        var loadDiagnostics = LoadElaborationGuard.CreateUnavailableDiagnostics(syntaxResult.SyntaxRoot);

        if (loadDiagnostics.Count > 0)
        {
            diagnostics.AddRange(loadDiagnostics);
            return new FrontEndResult(syntaxResult.SyntaxRoot, diagnostics);
        }

        return FinalizeElaboration(syntaxResult.SyntaxRoot, diagnostics);
    }

    private static FrontEndResult ProcessWithModuleElaboration(
        SyntaxParseResult syntaxResult,
        Func<string, string>? downloadCode,
        IEnumerable<string>? allowedHosts,
        SourceProcessingBudget budget)
    {
        var diagnostics = new List<Diagnostic>(syntaxResult.Diagnostics);

        var loadDiagnosticStart = diagnostics.Count;
        var loader = new ModuleLoader(diagnostics, downloadCode, allowedHosts, budget);
        var loadElaboratedRoot = loader.Elaborate(syntaxResult.SyntaxRoot);
        var loadDiagnosticsEnd = diagnostics.Count;

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
                    .Any(static d => d.Severity == DiagnosticSeverity.Error));
    }

    private static FrontEndResult FinalizeElaboration(
        Algorithm loadElaboratedRoot,
        List<Diagnostic> diagnostics,
        bool canEvaluateAfterLoadErrors = false)
    {
        var (parameterizedRoot, parameterDiagnostics) = ParameterDetector.Detect(loadElaboratedRoot);
        diagnostics.AddRange(parameterDiagnostics);

        var implicitResolvedRoot = ImplicitArgumentResolver.Resolve(parameterizedRoot);
        var propertyExposedRoot = PropertyExposureResolver.Resolve(implicitResolvedRoot);
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
