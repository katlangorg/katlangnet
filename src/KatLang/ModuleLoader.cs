namespace KatLang;

/// <summary>
/// Elaboration pass that resolves <c>load("url")</c> calls at compile time.
/// Runs AFTER parsing but BEFORE parameter detection and evaluation.
///
/// <para>
/// <c>load</c> is a compile-time directive, NOT a runtime function.
/// After this pass completes, no load calls remain in the AST — they are replaced
/// with <see cref="Expr.Block"/> nodes containing the parsed remote algorithm.
/// </para>
///
/// <para>Security: enforces domain allowlist, size limits, and cycle detection.</para>
/// </summary>
public sealed class ModuleLoader
{
    /// <summary>Maximum allowed source size in bytes (2 MB).</summary>
    private const int MaxSourceSize = 2 * 1024 * 1024;

    private readonly Func<string, string> _downloadCode;
    private readonly HashSet<string> _allowedHosts;
    private readonly Dictionary<string, Algorithm> _cache = new();
    private readonly HashSet<string> _inProgress = new();
    private readonly List<Diagnostic> _diagnostics;

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
    public ModuleLoader(
        List<Diagnostic> diagnostics,
        Func<string, string>? downloadCode = null,
        IEnumerable<string>? allowedHosts = null)
    {
        _diagnostics = diagnostics;
        _downloadCode = downloadCode ?? DefaultDownloadCode;
        _allowedHosts = allowedHosts is not null
            ? new HashSet<string>(allowedHosts, StringComparer.OrdinalIgnoreCase)
            : new HashSet<string>(StringComparer.OrdinalIgnoreCase) { "katlang.org" };
    }

    // ── Public API ───────────────────────────────────────────────────────────

    /// <summary>
    /// Processes the entire AST, resolving all load calls.
    /// Returns a new AST with load calls replaced by Block nodes.
    /// </summary>
    public Algorithm Elaborate(Algorithm root)
    {
        return ProcessAlgorithm(root, LoadContext.TopLevel);
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

    private Algorithm ProcessAlgorithm(Algorithm alg, LoadContext context)
    {
        if (alg is Algorithm.Builtin) return alg;

        var newOpens = new List<Expr>(alg.Opens.Count);
        foreach (var open in alg.Opens)
            newOpens.Add(ProcessExpr(open, LoadContext.OpenList));

        var newProperties = new List<Property>(alg.Properties.Count);
        foreach (var prop in alg.Properties)
        {
            var processedValue = ProcessAlgorithm(prop.Value, LoadContext.PropertyDef);
            // Unwrap only algorithm-valued single-block property bodies. This keeps
            // plain grouped values such as (a, b) wrapped as one block value while
            // still letting load-elaborated modules become direct property values.
            processedValue = UnwrapSingleBlock(processedValue);
            newProperties.Add(new Property(prop.Name, processedValue, prop.IsPublic));
        }

        var newOutput = new List<Expr>(alg.Output.Count);
        foreach (var expr in alg.Output)
        {
            // In a property definition or open list body, output is allowed for load
            // At top-level, output is runtime
            var outputCtx = context is LoadContext.PropertyDef or LoadContext.OpenList
                ? LoadContext.PropertyDef
                : LoadContext.RuntimeExpr;
            newOutput.Add(ProcessExpr(expr, outputCtx));
        }

        var result = alg with
        {
            Opens = newOpens,
            Properties = newProperties,
            Output = newOutput,
        };

        return result;
    }

    /// <summary>
    /// If an algorithm has no params, opens, or properties and its only output is an
    /// algorithm-valued Block, unwrap to use the block's algorithm directly. This mirrors
    /// ParseOutputLine's behavior for property bodies while preserving plain grouped values.
    /// </summary>
    private static Algorithm UnwrapSingleBlock(Algorithm alg)
    {
        if (alg is Algorithm.User
            {
                Params.Count: 0, Opens.Count: 0, Properties.Count: 0,
                Output: [Expr.Block(var innerAlg)]
            }
            && ShouldUnwrapPropertyBlock(innerAlg))
        {
            return innerAlg with { IsParametrized = alg.IsParametrized || innerAlg.IsParametrized };
        }
        return alg;
    }

    private static bool ShouldUnwrapPropertyBlock(Algorithm innerAlg)
        => innerAlg.IsParametrized
            || innerAlg.Properties.Count > 0
            || innerAlg.Opens.Count > 0;

    // ── Expression processing ────────────────────────────────────────────────

    private Expr ProcessExpr(Expr expr, LoadContext context)
    {
        switch (expr)
        {
            case Expr.Call(Expr.Resolve("load"), var args):
                return ProcessLoad(args, context, expr.Span);

            case Expr.Call(var func, var args):
                return new Expr.Call(
                    ProcessExpr(func, LoadContext.RuntimeExpr),
                    ProcessAlgorithm(args, LoadContext.RuntimeExpr))
                { Span = expr.Span };

            case Expr.Block(var alg):
                return new Expr.Block(ProcessAlgorithm(alg, context)) { Span = expr.Span };

            case Expr.Binary(var op, var left, var right):
                return new Expr.Binary(op,
                    ProcessExpr(left, LoadContext.RuntimeExpr),
                    ProcessExpr(right, LoadContext.RuntimeExpr))
                { Span = expr.Span };

            case Expr.Unary(var op, var operand):
                return new Expr.Unary(op, ProcessExpr(operand, LoadContext.RuntimeExpr))
                { Span = expr.Span };

            case Expr.Index(var target, var selector):
                return new Expr.Index(
                    ProcessExpr(target, LoadContext.RuntimeExpr),
                    ProcessExpr(selector, LoadContext.RuntimeExpr))
                { Span = expr.Span };

            case Expr.Combine(var left, var right):
                return new Expr.Combine(
                    ProcessExpr(left, context),
                    ProcessExpr(right, context))
                { Span = expr.Span };

            case Expr.DotCall(var target, var name, var args):
                return new Expr.DotCall(
                    ProcessExpr(target, args is null ? context : LoadContext.RuntimeExpr),
                    name,
                    args is not null ? ProcessAlgorithm(args, LoadContext.RuntimeExpr) : null)
                { Span = expr.Span };

            case Expr.Grace(var inner, var weight):
                return new Expr.Grace(ProcessExpr(inner, context), weight) { Span = expr.Span };

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

    private Expr ProcessLoad(Algorithm args, LoadContext context, SourceSpan? span)
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

        // 5. Cache check
        if (_cache.TryGetValue(normalized, out var cached))
            return new Expr.Block(cached) { Span = span };

        // 6. Fetch + parse + splice
        return FetchAndSplice(normalized, span);
    }

    /// <summary>
    /// Extracts a URL string from load arguments.
    /// Must be exactly one argument that is a string literal.
    /// </summary>
    private string? ExtractLoadUrl(Algorithm args, SourceSpan? span)
    {
        // load must have exactly 1 output (the URL) and no properties
        if (args.Properties.Count != 0 || args.Output.Count != 1)
        {
            ReportError("load requires exactly 1 argument (a URL string literal).", span);
            return null;
        }

        var urlExpr = args.Output[0];

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
    /// </summary>
    private Expr FetchAndSplice(string normalizedUrl, SourceSpan? span)
    {
        _inProgress.Add(normalizedUrl);
        try
        {
            // Fetch
            string source;
            try
            {
                source = _downloadCode(normalizedUrl);
            }
            catch (Exception ex)
            {
                ReportError($"load: failed to fetch '{normalizedUrl}': {ex.Message}", span);
                return new Expr.Num(0) { Span = span };
            }

            // Size check
            if (source.Length > MaxSourceSize)
            {
                ReportError(
                    $"load: source from '{normalizedUrl}' exceeds size limit ({source.Length} > {MaxSourceSize} bytes).",
                    span);
                return new Expr.Num(0) { Span = span };
            }

            // Parse the fetched source using the same parser (re-entrant)
            var parseResult = Parser.ParseSyntax(source);

            // Propagate any parse diagnostics (with context)
            foreach (var diag in parseResult.Diagnostics)
            {
                _diagnostics.Add(new Diagnostic(
                    $"[while loading {normalizedUrl}] {diag.Message}",
                    diag.Severity,
                    diag.Span));
            }

            if (parseResult.HasErrors)
            {
                ReportError($"load: parse errors in '{normalizedUrl}'.", span);
                return new Expr.Num(0) { Span = span };
            }

            // Recursively elaborate any load calls in the fetched module
            var elaborated = ProcessAlgorithm(parseResult.Root, LoadContext.TopLevel);

            // Cache the result
            _cache[normalizedUrl] = elaborated;

            return new Expr.Block(elaborated) { Span = span };
        }
        finally
        {
            _inProgress.Remove(normalizedUrl);
        }
    }

    // ── Default downloader ──────────────────────────────────────────────────

    /// <summary>
    /// Default synchronous HTTP downloader using HttpClient.
    /// </summary>
    private static string DefaultDownloadCode(string url)
    {
        using var client = new HttpClient();
        client.Timeout = TimeSpan.FromSeconds(10);
        return client.GetStringAsync(url).GetAwaiter().GetResult();
    }

    // ── Error reporting ──────────────────────────────────────────────────────

    private void ReportError(string message, SourceSpan? span)
    {
        _diagnostics.Add(new Diagnostic(
            message,
            DiagnosticSeverity.Error,
            span ?? new SourceSpan(1, 1, 1, 1)));
    }
}
