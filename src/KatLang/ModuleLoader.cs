namespace KatLang;

/// <summary>
/// Elaboration pass that resolves <c>load("url")</c> calls at compile time.
/// Runs AFTER parsing but BEFORE parameter detection and evaluation.
///
/// <para>
/// <c>load</c> is a compile-time directive, NOT a runtime function.
/// After this pass completes, no load calls remain in the AST — they are replaced
/// with <see cref="Expr.AlgorithmExpr"/> nodes containing the parsed remote algorithm.
/// </para>
///
/// <para>Security: enforces domain allowlist, size limits, cycle detection, and optional
/// host cancellation during source/module processing.</para>
/// </summary>
public sealed class ModuleLoader
{
    private readonly Func<string, CancellationToken, string> _downloadCode;
    private readonly CancellationToken _sourceProcessingCancellationToken;
    private readonly HashSet<string> _allowedHosts;
    private readonly Dictionary<string, Algorithm> _cache = new();
    private readonly HashSet<string> _inProgress = new();
    private readonly List<Diagnostic> _diagnostics;

    // Run-scoped host-runtime budget: import depth, distinct-module count, per-module and aggregate
    // source length. Its immutable SourceProcessingLimits carry the effective ceilings; the mutable
    // counters are private to this run. The per-module source ceiling here (EffectiveMaxSourceLength)
    // replaces the former fixed 2 MiB "bytes" constant and is now measured in UTF-16 code units,
    // consistent with the main-program ceiling.
    private readonly SourceProcessingBudget _budget;

    /// <summary>
    /// Cumulative structural traversal ceiling for this loader's OWN recursive walk
    /// (<see cref="ProcessAlgorithm(Algorithm, LoadContext, int)"/> /
    /// <see cref="ProcessExpr"/>), counting live levels ACROSS nested module loads: a
    /// nested load elaborates the fetched module while every parent traversal frame is
    /// still on the CLR stack, so per-module gating alone cannot bound the stack — a
    /// permitted chain of modules whose loads sit under deep container nesting stacks
    /// its levels multiplicatively. Process-isolated probes measured this walk's
    /// failure boundary on a 1 MiB thread at ~1,600-1,700 counted levels (Debug) and
    /// ~1,300-1,600 (Release) on its worst per-level shape, so 640 — the raw-syntax
    /// structural cap every single parsed module already satisfies — keeps a ≥2.0x
    /// margin in both configurations while admitting every previously supported
    /// ordinary module chain (top-level opens contribute only a few levels per module).
    ///
    /// <para><b>Nested parses are covered too:</b> a nested module's PARSE also runs
    /// while the ancestor traversal frames are live, so every nested
    /// <c>Parser.ParseSyntax</c> call starts with a conservative stack DEBT converted
    /// from the live traversal levels (<see cref="NestedParseStackDebt"/>). The
    /// parser's own cumulative recursion budget (<c>Parser.MaxNestingDepth</c>, held
    /// to under half of a 1 MiB stack on its worst measured shape) then bounds
    /// loader frames plus parser frames together, so no module source accepted for
    /// parsing at any permitted load position can overflow the documented envelope.</para>
    /// </summary>
    internal const int MaxTraversalDepth = AstStructuralPreflight.RawSyntaxMaxAstDepth;

    /// <summary>
    /// Fixed per-nesting allowance for the constant intermediate frames between a
    /// parent traversal and a nested module's traversal
    /// (<see cref="ProcessLoad"/> / <see cref="FetchAndSplice"/> plus parser entry).
    /// </summary>
    private const int NestedSpliceFrameAllowance = 4;

    /// <summary>
    /// Minimum parser recursion budget (in <c>Parser</c> stack units) a nested module
    /// parse must have left after the loader's stack debt: even the smallest module
    /// (<c>public X = 1</c>) needs a few units, so when the debt leaves less than
    /// this, the load is rejected BEFORE downloading — known active stack debt already
    /// makes safe parsing impossible.
    /// </summary>
    private const int MinNestedParseBudget = 8;

    /// <summary>
    /// Converts live loader traversal levels into parser stack-debt units for the
    /// nested module parse that runs ABOVE those frames. Measured per-level loader
    /// cost is at most ~0.8 KB across the measured Debug/Release boundaries
    /// (~1,300-1,700 levels per MiB), and one parser unit costs at most ~1.25 KB
    /// after the parser's per-shape weighting, so charging 2/3 unit per loader
    /// level models each level at ~0.83 KB — conservatively ABOVE the worst measured
    /// cost. Combined proof: for any live base B ≤
    /// <see cref="MaxTraversalDepth"/>, loader bytes (~0.8 KB x B) plus worst-case
    /// parser bytes (~1.25 KB x (384 - 2B/3)) stay at or below ~480 KB — below half
    /// of the documented 1 MiB minimum thread stack in both configurations.
    /// </summary>
    internal static int NestedParseStackDebt(int traversalBase)
    {
        if (traversalBase <= 0)
            return 0;

        var debt = ((long)traversalBase * 2 + 2) / 3;
        return debt >= int.MaxValue ? int.MaxValue : (int)debt;
    }

    /// <summary>
    /// Counted traversal levels held live by ancestor module elaborations while a
    /// nested module is being processed. Adjusted around the nested
    /// <see cref="ProcessAlgorithm(Algorithm, LoadContext, int)"/> call with
    /// <c>finally</c> restore, so downloader failures, cancellation, and nested
    /// rejections can never leak or corrupt it. Cache hits splice without
    /// re-traversal and charge nothing.
    /// </summary>
    private int _nestedTraversalBase;

    /// <summary>
    /// True when this elaboration emitted a source/module resource-policy diagnostic. Engine runs
    /// use this to avoid evaluating placeholder AST nodes merely to append unrelated evaluator
    /// context to a pre-evaluation resource rejection.
    /// </summary>
    internal bool HasSourceProcessingErrors { get; private set; }

    /// <summary>Run-local state exposed internally for cleanup-invariant regression tests.</summary>
    internal int InProgressModuleCount => _inProgress.Count;

    /// <summary>Run-local state exposed internally for cache-commit regression tests.</summary>
    internal int CachedModuleCount => _cache.Count;

    /// <summary>
    /// Creates a new ModuleLoader.
    /// </summary>
    /// <param name="diagnostics">Mutable diagnostics list shared with the parser.</param>
    /// <param name="downloadCode">
    /// Injected code fetcher: URL → source text.
    /// In WASM, caller supplies a JS interop implementation.
    /// If null, a default HttpClient-based fetcher is used.
    /// </param>
    /// <param name="allowedHosts">
    /// Set of allowed hostnames. Defaults to katlang.org only.
    /// </param>
    /// <remarks>
    /// One loader instance is one module-elaboration scope: its cache and default budget are shared
    /// by every <see cref="Elaborate"/> call on that instance. Because this AST-based constructor
    /// does not receive the original main-source text, its aggregate budget covers imported module
    /// source only. Normal parse/run entry points create an internal loader with the main source
    /// already charged.
    /// </remarks>
    public ModuleLoader(
        List<Diagnostic> diagnostics,
        Func<string, string>? downloadCode = null,
        IEnumerable<string>? allowedHosts = null)
        : this(
            diagnostics,
            downloadCode,
            downloadCodeWithCancellation: null,
            allowedHosts,
            budget: null,
            CancellationToken.None)
    {
    }

    /// <summary>
    /// Creates a loader whose module fetches and source processing observe host cancellation.
    /// </summary>
    /// <param name="diagnostics">Mutable diagnostics list shared with the parser.</param>
    /// <param name="sourceProcessingCancellationToken">
    /// Host cancellation for module fetching, parsing, and recursive module elaboration. It does
    /// not apply to evaluator computation performed after elaboration.
    /// </param>
    /// <param name="downloadCodeWithCancellation">
    /// Optional token-aware code fetcher. The configured token is passed unchanged. If null, the
    /// default HttpClient downloader is used with the same token and its existing ten-second
    /// timeout.
    /// </param>
    /// <param name="allowedHosts">
    /// Set of allowed hostnames. Defaults to katlang.org only.
    /// </param>
    /// <remarks>
    /// An <see cref="OperationCanceledException"/> is propagated only when
    /// <paramref name="sourceProcessingCancellationToken"/> has been cancelled. Downloader
    /// cancellation or timeout while that token is not cancelled is reported as the ordinary
    /// <c>load: failed to fetch</c> diagnostic. This factory leaves the existing constructor
    /// signature and overload resolution unchanged for source compatibility.
    /// </remarks>
    public static ModuleLoader CreateWithCancellation(
        List<Diagnostic> diagnostics,
        CancellationToken sourceProcessingCancellationToken,
        Func<string, CancellationToken, string>? downloadCodeWithCancellation = null,
        IEnumerable<string>? allowedHosts = null)
        => new(
            diagnostics,
            downloadCode: null,
            downloadCodeWithCancellation,
            allowedHosts,
            budget: null,
            sourceProcessingCancellationToken);

    /// <summary>
    /// Front-end entry point that threads the run-scoped <see cref="SourceProcessingBudget"/> so
    /// import depth, distinct-module count, and aggregate source are accounted across the whole run.
    /// The public constructor delegates here with a fresh default budget, so a directly-constructed
    /// loader still enforces the always-active ceilings.
    /// </summary>
    internal ModuleLoader(
        List<Diagnostic> diagnostics,
        Func<string, string>? downloadCode,
        Func<string, CancellationToken, string>? downloadCodeWithCancellation,
        IEnumerable<string>? allowedHosts,
        SourceProcessingBudget? budget,
        CancellationToken sourceProcessingCancellationToken)
    {
        _diagnostics = diagnostics;
        _downloadCode = downloadCodeWithCancellation
            ?? (downloadCode is not null
                ? (url, _) => downloadCode(url)
                : DefaultDownloadCode);
        _sourceProcessingCancellationToken = sourceProcessingCancellationToken;
        _allowedHosts = allowedHosts is not null
            ? new HashSet<string>(allowedHosts, StringComparer.OrdinalIgnoreCase)
            : new HashSet<string>(StringComparer.OrdinalIgnoreCase) { "katlang.org" };
        _budget = budget ?? new SourceProcessingBudget(null);
    }

    // ── Public API ───────────────────────────────────────────────────────────

    /// <summary>
    /// Processes the entire AST, resolving all load calls.
    /// Returns a new AST with load calls replaced by Block nodes.
    ///
    /// <para><b>Host-AST contract:</b> the root may be a preconstructed (host-built)
    /// AST. A non-recursive structural preflight runs BEFORE this pass's recursive
    /// traversal: a tree deeper than the raw-syntax structural cap (which every
    /// parsed module already satisfies, and which this walk was measured to survive
    /// with a ≥2x stack margin on the documented 1 MiB thread baseline — see
    /// <see cref="MaxTraversalDepth"/>), or a cyclic node graph, is rejected with one
    /// structured diagnostic and a placeholder root instead of being walked at
    /// process-terminating risk. Nested module loads are additionally bounded
    /// CUMULATIVELY: a load site's own traversal depth counts against the same
    /// ceiling for the module it loads, so stacked nested loads cannot multiply past
    /// the measured envelope.</para>
    /// </summary>
    /// <exception cref="OperationCanceledException">
    /// The source-processing token configured through <see cref="CreateWithCancellation"/> was
    /// cancelled.
    /// </exception>
    public Algorithm Elaborate(Algorithm root)
    {
        _sourceProcessingCancellationToken.ThrowIfCancellationRequested();

        // Structural safety boundary for this recursive consumer: checked iteratively
        // before any recursive frame, cycle-aware, judging shared subtrees by their
        // longest path. Trees the front-end pipeline hands in are ParseSyntax-gated to
        // the same cap and always pass unchanged.
        if (AstStructuralPreflight.Check(
                root,
                MaxTraversalDepth,
                AstConsumerProfile.FullyRecursive) is { } structuralRejection)
        {
            ReportSourceProcessingDiagnostic(AstStructuralPreflight.ToParseDiagnostic(
                structuralRejection, MaxTraversalDepth));
            return new Algorithm.User(null, [], [], [], []);
        }

        var elaborated = ProcessAlgorithm(root, LoadContext.TopLevel, depth: 1);
        _sourceProcessingCancellationToken.ThrowIfCancellationRequested();

        // Cache hits deliberately skip fetch, parse, and recursive loader traversal,
        // but a module cached at a shallow site may later be spliced under a much
        // deeper path. Re-check the FINISHED composition before this public boundary
        // returns it. The front-end pipeline repeats the same gate before its own
        // recursive load-invariant walk; this local check also protects callers that
        // use ModuleLoader directly.
        if (AstStructuralPreflight.Check(
                elaborated,
                MaxTraversalDepth,
                AstConsumerProfile.FullyRecursive) is { } compositionRejection)
        {
            ReportSourceProcessingDiagnostic(AstStructuralPreflight.ToParseDiagnostic(
                compositionRejection, MaxTraversalDepth));
            return new Algorithm.User(null, [], [], [], []);
        }

        return elaborated;
    }

    // ── Context tracking ────────────────────────────────────────────────────

    /// <summary>
    /// Tracks where a load call appears to enforce position restrictions.
    /// </summary>
    private enum LoadContext
    {
        /// <summary>Top-level algorithm body.</summary>
        TopLevel,
        /// <summary>Right-hand side of a property definition (allowed).</summary>
        PropertyDef,
        /// <summary>Inside an Open list (allowed).</summary>
        OpenList,
        /// <summary>Inside a runtime expression (NOT allowed).</summary>
        RuntimeExpr,
    }

    // ── Algorithm processing ─────────────────────────────────────────────────

    // The `depth` parameter mirrors the structural preflight's counting exactly (every
    // Expr/Algorithm node is one level; Property is a pass-through membrane), so the
    // cumulative nested-load guard in FetchAndSplice can judge the LIVE traversal
    // stack — parent frames plus the nested module's own depth — against the measured
    // ceiling. Frame-local by construction: no cleanup is needed on unwind.
    private Algorithm ProcessAlgorithm(Algorithm alg, LoadContext context, int depth)
    {
        _sourceProcessingCancellationToken.ThrowIfCancellationRequested();

        if (alg is Algorithm.Builtin) return alg;

        var newOpens = new List<Expr>(alg.Opens.Count);
        foreach (var open in alg.Opens)
            newOpens.Add(ProcessExpr(open, LoadContext.OpenList, depth + 1));

        var newProperties = new List<Property>(alg.Properties.Count);
        foreach (var prop in alg.Properties)
        {
            var processedValue = ProcessAlgorithm(prop.Value, LoadContext.PropertyDef, depth + 1);
            // Unwrap only algorithm-valued single-block property bodies. A plain
            // sequence value such as (a, b) stays one captured value boundary,
            // while load-elaborated modules become direct property values.
            processedValue = processedValue.UnwrapSingleBlockPropertyBody();
            newProperties.Add(prop.WithValue(processedValue));
        }

        var newOutput = new List<Expr>(alg.Output.Count);
        foreach (var expr in alg.Output)
        {
            // In a property definition or open list body, output is allowed for load
            // At top-level, output is runtime
            var outputCtx = context is LoadContext.PropertyDef or LoadContext.OpenList
                ? LoadContext.PropertyDef
                : LoadContext.RuntimeExpr;
            newOutput.Add(ProcessExpr(expr, outputCtx, depth + 1));
        }

        var result = alg with
        {
            Opens = newOpens,
            Properties = newProperties,
            Output = newOutput,
        };

        return result;
    }

    // ── Expression processing ────────────────────────────────────────────────

    private Expr ProcessExpr(Expr expr, LoadContext context, int depth)
    {
        if (expr.TryGetUnresolvedLoadArguments(out var loadArgs))
            return ProcessLoad(loadArgs, context, expr.Span, depth);

        switch (expr)
        {
            case Expr.Call(var func, var args):
                return new Expr.Call(
                    ProcessExpr(func, LoadContext.RuntimeExpr, depth + 1),
                    new OutputBundle(args.Select(argExpr => ProcessExpr(argExpr, LoadContext.RuntimeExpr, depth + 1)).ToList()))
                { Span = expr.Span };

            case Expr.AlgorithmExpr(var alg):
                return new Expr.AlgorithmExpr(ProcessAlgorithm(alg, context, depth + 1)) { Span = expr.Span };

            // Capture rows inherit the surrounding load context, exactly like
            // list-literal elements and internal sequence joins: `X = (load('url'), 1)`
            // elaborates where `X = [load('url')]` does.
            case Expr.Capture(var captureBody):
                return new Expr.Capture(new OutputBundle(
                    captureBody.Select(row => ProcessExpr(row, context, depth + 1)).ToList()))
                { Span = expr.Span };

            case Expr.Binary(var op, var left, var right):
                return new Expr.Binary(op,
                    ProcessExpr(left, LoadContext.RuntimeExpr, depth + 1),
                    ProcessExpr(right, LoadContext.RuntimeExpr, depth + 1))
                { Span = expr.Span };

            case Expr.Unary(var op, var operand):
                return new Expr.Unary(op, ProcessExpr(operand, LoadContext.RuntimeExpr, depth + 1))
                { Span = expr.Span };

            case Expr.Index(var target, var selector):
                return new Expr.Index(
                    ProcessExpr(target, LoadContext.RuntimeExpr, depth + 1),
                    ProcessExpr(selector, LoadContext.RuntimeExpr, depth + 1))
                { Span = expr.Span };

            case Expr.SequenceSpread(var operand):
                return new Expr.SequenceSpread(
                    ProcessExpr(operand, context, depth + 1))
                {
                    Span = expr.Span,
                    SpreadMarkerSpan = ((Expr.SequenceSpread)expr).SpreadMarkerSpan,
                };

            case Expr.SequenceConstruct(var left, var right):
                return new Expr.SequenceConstruct(
                    ProcessExpr(left, context, depth + 1),
                    ProcessExpr(right, context, depth + 1))
                { Span = expr.Span };

            // List-literal elements inherit the surrounding load context,
            // exactly like capture rows (Expr.Capture) and internal sequence
            // joins: `X = [load('url')]` elaborates where
            // `X = (load('url'), 1)` does.
            case Expr.ListLiteral(var items):
                return new Expr.ListLiteral(
                    items.Select(item => ProcessExpr(item, context, depth + 1)).ToList())
                { Span = expr.Span };

            case Expr.DotCall dotCall:
                // `with` keeps every stored dot-edge fact (member span,
                // lexical fallback) intact — rebuilding positionally here
                // silently dropped the elaborated fallback identity for every
                // module-elaborated tree.
                return dotCall with
                {
                    Target = ProcessExpr(dotCall.Target, dotCall.Args is null ? context : LoadContext.RuntimeExpr, depth + 1),
                    Args = dotCall.Args is { } dotArgs
                        ? new OutputBundle(dotArgs.Select(argExpr => ProcessExpr(argExpr, LoadContext.RuntimeExpr, depth + 1)).ToList())
                        : null,
                };

            case Expr.Grace grace:
                // `with` keeps the stored Grace weight intact — module
                // elaboration runs BEFORE parameter detection, so the
                // annotation is still live here.
                return grace with { Inner = ProcessExpr(grace.Inner, context, depth + 1) };

            // Leaf nodes — no transformation needed
            case Expr.Resolve:
            case Expr.Param:
            case Expr.Num:
            case Expr.StringLiteral:
            case Expr.NativeCall:
                return expr;

            default:
                return expr;
        }
    }

    // ── load processing ────────────────────────────────────────────────────────────────

    private Expr ProcessLoad(OutputBundle args, LoadContext context, SourceSpan? span, int depth)
    {
        // 1. Position check: load only allowed in property definitions and open lists
        if (context == LoadContext.RuntimeExpr)
        {
            ReportError("load not allowed in runtime expression.", span);
            return new Expr.Num(0) { Span = span };
        }

        // 2. Extract URL: must be exactly 1 argument, must be a string literal
        var url = ExtractLoadUrl(args, span);
        if (url is null)
            return new Expr.Num(0) { Span = span };

        // 3. Domain check
        if (!IsAllowedUrl(url, span))
            return new Expr.Num(0) { Span = span };

        // 4. Cycle detection
        var normalized = NormalizeUrl(url);
        if (_inProgress.Contains(normalized))
        {
            ReportError($"load cycle detected: {normalized}", span);
            return new Expr.Num(0) { Span = span };
        }

        // 5. Cache check — an already-elaborated module splices without re-traversal,
        // so it charges no cumulative traversal depth.
        if (_cache.TryGetValue(normalized, out var cached))
            return new Expr.AlgorithmExpr(cached) { Span = span };

        // 6. Fetch + parse + splice
        return FetchAndSplice(normalized, span, depth);
    }

    /// <summary>
    /// Extracts a URL string from load arguments.
    /// Must be exactly one argument that is a string literal.
    /// </summary>
    private string? ExtractLoadUrl(OutputBundle args, SourceSpan? span)
    {
        // load must have exactly 1 argument slot (the URL)
        if (args.Count != 1)
        {
            ReportError("load requires exactly 1 argument (a URL string literal).", span);
            return null;
        }

        var urlExpr = args[0];

        // Must be a string literal
        if (urlExpr is Expr.StringLiteral(var url))
            return url;

        // Not a literal — could be Resolve("url"), a variable, or any other expression
        ReportError("load URL must be a literal (non-dynamic).", span);
        return null;
    }

    /// <summary>
    /// Validates that the URL is well-formed and the host is in the allowlist.
    /// </summary>
    private bool IsAllowedUrl(string url, SourceSpan? span)
    {
        if (!Uri.TryCreate(url, UriKind.Absolute, out var uri))
        {
            ReportError($"load: invalid URL '{url}'.", span);
            return false;
        }

        if (uri.Scheme != "https")
        {
            ReportError($"load: only HTTPS URLs are allowed (got '{uri.Scheme}').", span);
            return false;
        }

        var host = uri.Host;

        // Check exact match or subdomain match
        foreach (var allowed in _allowedHosts)
        {
            if (string.Equals(host, allowed, StringComparison.OrdinalIgnoreCase))
                return true;
            if (host.EndsWith("." + allowed, StringComparison.OrdinalIgnoreCase))
                return true;
        }

        ReportError($"load: domain not allowed: '{host}'.", span);
        return false;
    }

    /// <summary>Normalizes a URL for caching and cycle detection.</summary>
    private static string NormalizeUrl(string url)
    {
        if (Uri.TryCreate(url, UriKind.Absolute, out var uri))
            return uri.AbsoluteUri;
        return url;
    }

    /// <summary>
    /// Fetches remote source code, parses it, runs load elaboration recursively,
    /// and returns a Block containing the loaded algorithm.
    /// <paramref name="depth"/> is the load site's own traversal depth within the
    /// module currently being processed; together with the traversal levels ancestor
    /// modules hold live it bounds the nested elaboration cumulatively (see
    /// <see cref="MaxTraversalDepth"/>).
    /// </summary>
    private Expr FetchAndSplice(string normalizedUrl, SourceSpan? span, int depth)
    {
        // Import-depth ceiling: descend one level, or turn a would-be host stack overflow into a
        // structured diagnostic. Only reached on a cache MISS, so it bounds the true chain depth.
        // Paired with ExitModule in the finally below.
        if (!_budget.TryEnterModule())
        {
            ReportSourceProcessingDiagnostic(SourceProcessingDiagnostics.ModuleImportDepthExceeded(
                normalizedUrl, _budget.CurrentDepth + 1, _budget.MaxModuleDepth, span));
            return new Expr.Num(0) { Span = span };
        }

        _inProgress.Add(normalizedUrl);
        var hasModuleSourceReservation = false;
        var reservedSourceLength = 0;
        try
        {
            // Distinct-module ceiling, checked BEFORE downloading a new module (this is a cache
            // miss). Checking capacity before the fetch means a run past the module-count ceiling
            // never pays for extra downloads. The reservation is committed below only once the
            // aggregate also fits, so a later-rejected load leaves the count unchanged.
            if (!_budget.CanReserveModule())
            {
                ReportSourceProcessingDiagnostic(SourceProcessingDiagnostics.ModuleCountExceeded(
                    normalizedUrl, _budget.ModuleCount + 1, _budget.MaxModuleCount, span));
                return new Expr.Num(0) { Span = span };
            }

            // Cumulative structural budget, pre-fetch half: when the parent traversal
            // levels alone exhaust the traversal ceiling — or leave the PARSER less
            // than a minimal useful recursion budget after the stack debt those live
            // levels impose — no module content could be admitted here, so reject
            // before paying for the download (matching the module-count check above).
            // The fetched tree itself is judged against the remaining traversal
            // allowance after parsing, below.
            var traversalBase = checked(_nestedTraversalBase + depth + NestedSpliceFrameAllowance);
            var nestedAllowance = MaxTraversalDepth - traversalBase;
            var parseStackDebt = NestedParseStackDebt(traversalBase);
            if (nestedAllowance < 1 || parseStackDebt > Parser.MaxNestingDepth - MinNestedParseBudget)
            {
                ReportSourceProcessingDiagnostic(SourceProcessingDiagnostics.ModuleNestingTooDeep(
                    normalizedUrl, MaxTraversalDepth, span));
                return new Expr.Num(0) { Span = span };
            }

            // Fetch
            string source;
            try
            {
                _sourceProcessingCancellationToken.ThrowIfCancellationRequested();
                source = _downloadCode(normalizedUrl, _sourceProcessingCancellationToken);
                _sourceProcessingCancellationToken.ThrowIfCancellationRequested();
            }
            catch (OperationCanceledException) when (_sourceProcessingCancellationToken.IsCancellationRequested)
            {
                throw;
            }
            catch (Exception ex)
            {
                // Host cancellation is authoritative even if the downloader surfaced a different
                // exception while reacting to it. Only a still-active host token permits a fetch
                // diagnostic (including downloader-owned cancellation/timeout exceptions).
                _sourceProcessingCancellationToken.ThrowIfCancellationRequested();
                ReportError($"load: failed to fetch '{normalizedUrl}': {ex.Message}", span);
                return new Expr.Num(0) { Span = span };
            }

            if (source is null)
            {
                ReportError($"load: fetch for '{normalizedUrl}' returned no source text.", span);
                return new Expr.Num(0) { Span = span };
            }

            // Per-module source-length ceiling, checked after download and before parsing, so an
            // oversized module never allocates tokens or nodes.
            if (!_budget.SourceLengthWithinLimit(source.Length))
            {
                ReportSourceProcessingDiagnostic(SourceProcessingDiagnostics.ModuleSourceLengthExceeded(
                    normalizedUrl, source.Length, _budget.MaxSourceLength, span));
                return new Expr.Num(0) { Span = span };
            }

            // Aggregate-source ceiling. Commit the aggregate and distinct-module reservations
            // together only once both fit — a rejected load leaves both counters unchanged. An
            // observed host cancellation rolls this active frame's reservation back while
            // unwinding, before the partial module can reach the cache.
            var requestedTotal = checked(_budget.AggregateSource + source.Length);
            if (!_budget.TryReserveModuleSource(source.Length))
            {
                ReportSourceProcessingDiagnostic(SourceProcessingDiagnostics.AggregateSourceLengthExceeded(
                    normalizedUrl,
                    source.Length,
                    requestedTotal,
                    _budget.MaxAggregateSourceLength,
                    span));
                return new Expr.Num(0) { Span = span };
            }

            hasModuleSourceReservation = true;
            reservedSourceLength = source.Length;

            // Parse the fetched source as raw syntax, then elaborate nested loads
            // locally. This parse RUNS ABOVE the loader's live traversal frames, so
            // it starts with the conservative stack debt computed before the fetch:
            // the parser's cumulative recursion budget then bounds loader frames plus
            // parser frames TOGETHER (see NestedParseStackDebt for the combined
            // stack proof). A module whose nesting no longer fits the indebted
            // budget is rejected by the parser at the crossing token, and reported
            // here on the established load channel at the load site.
            _sourceProcessingCancellationToken.ThrowIfCancellationRequested();
            var syntaxResult = Parser.ParseSyntax(source, parseStackDebt);

            if (syntaxResult.HasErrors)
            {
                ReportError(
                    HasStructuralBudgetDiagnostic(syntaxResult)
                        ? BuildLoadedSourceNestingErrorMessage(normalizedUrl)
                        : BuildLoadedSourceParseErrorMessage(normalizedUrl, source),
                    span);
                return new Expr.Num(0) { Span = span };
            }

            // Propagate any non-error diagnostics (with context).
            foreach (var diag in syntaxResult.Diagnostics)
            {
                _diagnostics.Add(new Diagnostic(
                    $"[while loading {normalizedUrl}] {diag.Message}",
                    diag.Severity,
                    diag.Span));
            }

            // Cumulative structural budget, post-parse half: the parent modules' live
            // traversal levels, this load site's own path depth, and the fixed splice
            // allowance all count against the one measured ceiling the loader's
            // recursion is proven safe under, so the fetched module's tree must fit
            // the REMAINING allowance. Judged iteratively BEFORE the nested recursive
            // traversal (the unsafe tree is never walked recursively and never
            // rendered into the diagnostic); an unsafe nesting is one structured
            // diagnostic and the load's established placeholder. The committed source
            // reservation deliberately stays charged, exactly like a module whose
            // content fails to parse.
            if (AstStructuralPreflight.Check(
                    syntaxResult.SyntaxRoot,
                    nestedAllowance,
                    AstConsumerProfile.FullyRecursive) is not null)
            {
                ReportSourceProcessingDiagnostic(SourceProcessingDiagnostics.ModuleNestingTooDeep(
                    normalizedUrl, MaxTraversalDepth, span));
                return new Expr.Num(0) { Span = span };
            }

            // Recursively elaborate any load calls in the fetched module
            _sourceProcessingCancellationToken.ThrowIfCancellationRequested();
            var previousTraversalBase = _nestedTraversalBase;
            _nestedTraversalBase = traversalBase;
            Algorithm elaborated;
            try
            {
                elaborated = ProcessAlgorithm(syntaxResult.SyntaxRoot, LoadContext.TopLevel, depth: 1);
            }
            finally
            {
                _nestedTraversalBase = previousTraversalBase;
            }

            // Cancellation never commits a partial module. This check also observes cancellation
            // requested during parsing or recursive elaboration before the cache write.
            _sourceProcessingCancellationToken.ThrowIfCancellationRequested();
            _cache[normalizedUrl] = elaborated;

            return new Expr.AlgorithmExpr(elaborated) { Span = span };
        }
        catch (OperationCanceledException) when (_sourceProcessingCancellationToken.IsCancellationRequested)
        {
            if (hasModuleSourceReservation)
                _budget.RollbackModuleSource(reservedSourceLength);

            throw;
        }
        finally
        {
            _inProgress.Remove(normalizedUrl);
            _budget.ExitModule();
        }
    }

    // ── Default downloader ──────────────────────────────────────────────────

    /// <summary>
    /// Default synchronous HTTP downloader using HttpClient.
    /// </summary>
    private static string DefaultDownloadCode(string url, CancellationToken cancellationToken)
    {
        using var client = new HttpClient();
        client.Timeout = TimeSpan.FromSeconds(10);
        return client.GetStringAsync(url, cancellationToken).GetAwaiter().GetResult();
    }

    // ── Error reporting ──────────────────────────────────────────────────────

    private static string BuildLoadedSourceParseErrorMessage(string normalizedUrl, string source)
    {
        var sourceDescription = LooksLikeHtml(source)
            ? "the URL returned HTML instead of KatLang source"
            : "the downloaded content is not valid KatLang source";

        return $"load: cannot load '{normalizedUrl}': {sourceDescription}. " +
            "Check that the URL is correct and points directly to a KatLang .kat file.";
    }

    /// <summary>
    /// True when a nested module's parse failed on the parser's cumulative recursion
    /// budget (which includes this loader's live-frame stack debt), so the failure is
    /// a position-dependent nesting rejection rather than invalid module content.
    /// </summary>
    private static bool HasStructuralBudgetDiagnostic(SyntaxParseResult syntaxResult)
        => syntaxResult.Diagnostics.Any(
            d => d.Message.Contains(Parser.NestingTooDeepMessage, StringComparison.Ordinal)
                || d.Message.Contains("structural AST depth limit", StringComparison.Ordinal));

    private static string BuildLoadedSourceNestingErrorMessage(string normalizedUrl)
        => $"load: loading '{normalizedUrl}' at this position would nest module source too deeply to parse safely "
            + "(cumulative structural budget across the module chain). "
            + "Move the load closer to the top level of its module, or split the module chain into smaller modules.";

    private static bool LooksLikeHtml(string source)
    {
        var trimmed = source.TrimStart();
        return trimmed.StartsWith("<!doctype", StringComparison.OrdinalIgnoreCase) ||
            trimmed.StartsWith("<html", StringComparison.OrdinalIgnoreCase) ||
            trimmed.StartsWith("<head", StringComparison.OrdinalIgnoreCase) ||
            trimmed.StartsWith("<body", StringComparison.OrdinalIgnoreCase);
    }

    private void ReportError(string message, SourceSpan? span)
    {
        _diagnostics.Add(new Diagnostic(
            message,
            DiagnosticSeverity.Error,
            span ?? new SourceSpan(1, 1, 1, 1)));
    }

    private void ReportSourceProcessingDiagnostic(Diagnostic diagnostic)
    {
        HasSourceProcessingErrors = true;
        _diagnostics.Add(diagnostic);
    }
}
