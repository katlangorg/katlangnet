using System.Runtime.CompilerServices;

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
/// <para><b>Async-only module acquisition:</b> source text is obtained through ONE
/// asynchronous contract, <c>Func&lt;string, CancellationToken, ValueTask&lt;string&gt;&gt;</c>.
/// <see cref="ElaborateAsync"/> genuinely suspends on an incomplete download and resumes
/// the elaboration at the same logical point when it completes — the downloader is never
/// re-invoked after a suspension, and there is no synchronous fetching path and no
/// blocking sync-over-async bridge anywhere in the loader. A downloader that completes
/// synchronously (for example <c>ValueTask.FromResult</c> over an in-memory map) keeps
/// the whole elaboration synchronous on the calling thread.</para>
///
/// <para><b>Traversal routing:</b> the rewrite walk exists in two lock-step forms. The
/// SYNCHRONOUS walk (<see cref="ProcessAlgorithm"/> / <see cref="ProcessExpr"/>) is the
/// stack-calibrated implementation and handles every subtree that contains no unresolved
/// load — it can never need to await. The ASYNC twins
/// (<see cref="ProcessAlgorithmAsync"/> / <see cref="ProcessExprAsync"/>) mirror it and
/// run only along load-bearing spines — the root-paths to unresolved load calls, marked
/// up front by one linear pre-scan (<see cref="MarkLoadBearing"/>) — so async
/// state-machine frames (measured several hundred bytes larger per level than the
/// calibrated synchronous frames) are spent only where a suspension is possible. Routing
/// happens per child through <see cref="RouteExprAsync"/> / <see cref="RouteAlgorithmAsync"/>.</para>
///
/// <para>Security: enforces domain allowlist, size limits, cycle detection, and optional
/// host cancellation during source/module processing.</para>
/// </summary>
public sealed class ModuleLoader
{
    private readonly Func<string, CancellationToken, ValueTask<string>> _downloadCode;
    private readonly CancellationToken _sourceProcessingCancellationToken;
    private readonly HashSet<string> _allowedHosts;
    private readonly Dictionary<string, Algorithm> _cache = new();
    private readonly HashSet<string> _inProgress = new();
    private readonly List<Diagnostic> _diagnostics;

    // Reference-identity set of nodes with an unresolved load call at or beneath them —
    // the load-bearing spines. Populated by MarkLoadBearing before each tree is walked
    // (the root in ElaborateAsync, each fetched module in FetchAndSpliceAsync); RouteExprAsync /
    // RouteAlgorithmAsync consult it to decide sync vs async processing per child. Marking is
    // path-complete: every node from which the rewrite walk can reach a load is marked, so the
    // synchronous walk (entered only at unmarked nodes) can never encounter a load.
    // The set is cleared at the public elaboration boundary so a reusable loader does
    // not retain every caller-owned input tree for the rest of its lifetime.
    private readonly HashSet<object> _loadBearing = new(ReferenceEqualityComparer.Instance);
    private readonly LoadBearingMarker _loadBearingMarker;

    // Run-scoped host-runtime budget: import depth, distinct-module count, per-module and aggregate
    // source length. Its immutable SourceProcessingLimits carry the effective ceilings; the mutable
    // counters are private to this run. The per-module source ceiling here (EffectiveMaxSourceLength)
    // replaces the former fixed 2 MiB "bytes" constant and is now measured in UTF-16 code units,
    // consistent with the main-program ceiling.
    private readonly SourceProcessingBudget _budget;

    /// <summary>
    /// Cumulative structural traversal ceiling for this loader's OWN recursive walk
    /// (<see cref="ProcessAlgorithm(Algorithm, LoadContext, int)"/> /
    /// <see cref="ProcessExpr"/> and their async twins), counting live levels ACROSS
    /// nested module loads: a nested load elaborates the fetched module while every
    /// parent traversal frame is still on the CLR stack, so per-module gating alone
    /// cannot bound the stack — a permitted chain of modules whose loads sit under
    /// deep container nesting stacks its levels multiplicatively. Process-isolated
    /// probes measured the SYNCHRONOUS walk's failure boundary on a 1 MiB thread at
    /// ~1,600-1,700 counted levels (Debug) and ~1,300-1,600 (Release) on its worst
    /// per-level shape, so 640 — the raw-syntax structural cap every single parsed
    /// module already satisfies — keeps a ≥2.0x margin in both configurations while
    /// admitting every previously supported ordinary module chain (top-level opens
    /// contribute only a few levels per module). Load-FREE subtrees always take that
    /// synchronous walk, so this calibration still holds for them unchanged; the
    /// async twin frames on load-bearing spines are heavier and their slack over the
    /// <see cref="NestedParseStackDebt"/> model is absorbed by the
    /// <see cref="ThrowIfInsufficientStack"/> reserve backstop (see the debt model's
    /// doc for the combined argument).
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
    /// (<see cref="ProcessLoadAsync"/> / <see cref="FetchAndSpliceAsync"/> plus
    /// routing and parser entry).
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
    /// nested module parse that runs ABOVE those frames. Charging 2/3 unit per
    /// level models each level at ~0.83 KB against the parser's ~1.25 KB/unit —
    /// above the measured worst synchronous per-level cost (~0.8 KB across the
    /// measured Debug/Release boundaries), and this multiplier is what admits every
    /// supported ordinary module chain (64 top-level nested imports accumulate
    /// ~420 counted live levels, which a larger multiplier would reject).
    ///
    /// <para><b>Async-frame slack is carried by the reserve backstop, not this
    /// model.</b> Live cross-fetch levels are exactly the load-bearing spine, which
    /// the loader walks through its ASYNC twins; their state-machine frames measure
    /// several hundred bytes above the calibrated synchronous frames, so the real
    /// per-level cost can exceed this model's ~0.83 KB. Two mechanisms keep that
    /// safe: every walk level probes the runtime's stack reserve
    /// (<see cref="ThrowIfInsufficientStack"/>), so a descent the model under-priced
    /// stops with a structured diagnostic instead of overflowing; and a nested parse
    /// is admitted only with <c>Parser.MaxNestingDepth − debt</c> units — near the
    /// debt ceiling that admitted budget (a few units ≈ KBs) is far below the
    /// reserve the last probed level guaranteed, while at shallow bases the real
    /// remaining stack dwarfs the admitted parse. The subprocess probes
    /// (<c>DeepNestedModuleChains_ProbeChild</c>, <c>NearBoundaryShapes_ProbeChild</c>)
    /// revalidate these boundary shapes on dedicated 1 MiB threads in both
    /// configurations.</para>
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
    /// nested module is being processed. Adjusted around the nested routed
    /// traversal call with <c>finally</c> restore, so downloader failures,
    /// cancellation, and nested rejections can never leak or corrupt it. Cache hits
    /// splice without re-traversal and charge nothing. The loader processes one
    /// logical elaboration sequentially (a suspension resumes the same walk, never a
    /// parallel one), so this stays a plain field across await boundaries.
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
    /// Injected asynchronous code fetcher: URL and the configured
    /// <paramref name="sourceProcessingCancellationToken"/> → source text. A host with the
    /// source already in memory returns <c>ValueTask.FromResult(text)</c> and the whole
    /// elaboration completes synchronously. If null, a default HttpClient-based fetcher is used
    /// with the same token and a ten-second timeout.
    /// </param>
    /// <param name="allowedHosts">
    /// Set of allowed hostnames. Defaults to katlang.org only.
    /// </param>
    /// <param name="sourceProcessingCancellationToken">
    /// Host cancellation for module fetching, parsing, and recursive module elaboration. The token
    /// is passed unchanged to <paramref name="downloadCode"/>. It does not apply to evaluator
    /// computation performed after elaboration.
    /// </param>
    /// <remarks>
    /// One loader instance is one module-elaboration scope: its cache and default budget are shared
    /// by every <see cref="ElaborateAsync"/> call on that instance. Because this AST-based
    /// constructor does not receive the original main-source text, its aggregate budget covers
    /// imported module source only. Normal parse/run entry points create an internal loader with
    /// the main source already charged.
    /// <para>An <see cref="OperationCanceledException"/> is propagated only when
    /// <paramref name="sourceProcessingCancellationToken"/> has been cancelled, and carries that
    /// exact token even if the downloader faulted with a different cancellation token. Downloader
    /// cancellation or timeout while the host token is not cancelled is reported as the ordinary
    /// <c>load: failed to fetch</c> diagnostic.</para>
    /// </remarks>
    public ModuleLoader(
        List<Diagnostic> diagnostics,
        Func<string, CancellationToken, ValueTask<string>>? downloadCode = null,
        IEnumerable<string>? allowedHosts = null,
        CancellationToken sourceProcessingCancellationToken = default)
        : this(
            diagnostics,
            downloadCode,
            allowedHosts,
            budget: null,
            sourceProcessingCancellationToken)
    {
    }

    /// <summary>
    /// Front-end entry point that threads the run-scoped <see cref="SourceProcessingBudget"/> so
    /// import depth, distinct-module count, and aggregate source are accounted across the whole run.
    /// The public constructor delegates here with a fresh default budget, so a directly-constructed
    /// loader still enforces the always-active ceilings.
    /// </summary>
    internal ModuleLoader(
        List<Diagnostic> diagnostics,
        Func<string, CancellationToken, ValueTask<string>>? downloadCode,
        IEnumerable<string>? allowedHosts,
        SourceProcessingBudget? budget,
        CancellationToken sourceProcessingCancellationToken)
    {
        _diagnostics = diagnostics;
        _downloadCode = downloadCode ?? DefaultDownloadCode;
        _sourceProcessingCancellationToken = sourceProcessingCancellationToken;
        _allowedHosts = allowedHosts is not null
            ? new HashSet<string>(allowedHosts, StringComparer.OrdinalIgnoreCase)
            : new HashSet<string>(StringComparer.OrdinalIgnoreCase) { "katlang.org" };
        _budget = budget ?? new SourceProcessingBudget(null);
        _loadBearingMarker = new LoadBearingMarker(_loadBearing);
    }

    // ── Public API ───────────────────────────────────────────────────────────

    /// <summary>
    /// Processes the entire AST, resolving all load calls, awaiting each module download.
    /// Returns a new AST with load calls replaced by algorithm-expression nodes.
    /// An incomplete download genuinely suspends the elaboration; it resumes at the same
    /// logical point when the download completes, and the downloader is invoked at most once
    /// per distinct successful module URL per loader instance.
    ///
    /// <para><b>Host-AST contract:</b> the root may be a preconstructed (host-built)
    /// AST. A non-recursive structural preflight runs BEFORE this pass's recursive
    /// traversal: a tree deeper than the raw-syntax structural cap (which every
    /// parsed module already satisfies, and which the synchronous walk was measured
    /// to survive with a ≥2x stack margin on the documented 1 MiB thread baseline —
    /// see <see cref="MaxTraversalDepth"/>), or a cyclic node graph, is rejected with
    /// one structured diagnostic and a placeholder root instead of being walked at
    /// process-terminating risk. Nested module loads are additionally bounded
    /// CUMULATIVELY: a load site's own traversal depth counts against the same
    /// ceiling for the module it loads, so stacked nested loads cannot multiply past
    /// the measured envelope. As a final fail-safe, both walks probe the runtime's
    /// stack reserve at every level (<see cref="ThrowIfInsufficientStack"/>): a
    /// host-built composition that outgrows the actual thread stack despite the
    /// structural gates is rejected with a structured diagnostic, never a process
    /// crash.</para>
    /// </summary>
    /// <exception cref="OperationCanceledException">
    /// The configured source-processing token was cancelled. Delivered through the returned
    /// task once the elaboration has started awaiting.
    /// </exception>
    public async ValueTask<Algorithm> ElaborateAsync(Algorithm root)
    {
        _sourceProcessingCancellationToken.ThrowIfCancellationRequested();
        try
        {
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

            Algorithm elaborated;
            try
            {
                MarkLoadBearing(root);
                elaborated = await RouteAlgorithmAsync(root, LoadContext.TopLevel, depth: 1).ConfigureAwait(false);
            }
            catch (ModuleElaborationStackException)
            {
                // The reserve backstop fired mid-walk: the composition outgrew the actual
                // thread stack despite the structural gates (for example a host thread
                // smaller than the documented 1 MiB envelope). Budget frames unwound
                // through their finally blocks; report one structured diagnostic and the
                // established placeholder root.
                ReportSourceProcessingDiagnostic(
                    SourceProcessingDiagnostics.ModuleElaborationStackExhausted(MaxTraversalDepth));
                return new Algorithm.User(null, [], [], [], []);
            }

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
        finally
        {
            _loadBearing.Clear();
        }
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

    // ── Load-bearing spine marking and routing ──────────────────────────────

    /// <summary>
    /// One linear pre-scan over <paramref name="root"/> that marks every node from
    /// which the rewrite walk can reach an unresolved load call (the load call itself
    /// plus its whole root-path). Marking stops upward at the first already-marked
    /// node — full-path marking makes "marked" upward-closed — so total marking work
    /// stays proportional to the marked spine. The scan's reach is a superset of the
    /// rewrite walk's reach (it is an <see cref="AstWalker"/>, which additionally
    /// visits patterns, conditional branches, and stored fallback identities the
    /// rewrite walk leaves untouched), so an UNMARKED node is proof its subtree
    /// elaborates without ever needing to await.
    /// </summary>
    private void MarkLoadBearing(Algorithm root) => _loadBearingMarker.VisitAlgorithm(root);

    private sealed class LoadBearingMarker(HashSet<object> marked) : AstWalker
    {
        private readonly List<object> _path = [];

        protected override bool VisitsExplicitParameterDeclarations => false;

        public override void VisitAlgorithm(Algorithm algorithm)
        {
            // The scan recurses the same depths the walks do (small walker frames,
            // preflight-gated), so it carries the same reserve backstop — on a host
            // thread below the documented envelope the scan must fail structured,
            // not by overflowing before the walk even starts.
            ThrowIfInsufficientStack();
            _path.Add(algorithm);
            try
            {
                base.VisitAlgorithm(algorithm);
            }
            finally
            {
                _path.RemoveAt(_path.Count - 1);
            }
        }

        public override void VisitExpr(Expr expr)
        {
            ThrowIfInsufficientStack();
            if (expr.TryGetUnresolvedLoadArguments(out _))
            {
                // Mark the load call and its live root-path; elaboration replaces the
                // whole call, so its argument slots are never walked. The upward stop
                // at the first already-marked node keeps repeated loads cheap.
                marked.Add(expr);
                for (var i = _path.Count - 1; i >= 0; i--)
                {
                    if (!marked.Add(_path[i]))
                        break;
                }

                return;
            }

            _path.Add(expr);
            try
            {
                base.VisitExpr(expr);
            }
            finally
            {
                _path.RemoveAt(_path.Count - 1);
            }
        }
    }

    /// <summary>
    /// Routes one child algorithm: a load-bearing subtree continues through the async
    /// twin (it may need to await a download), anything else takes the calibrated
    /// synchronous walk and completes inline.
    /// </summary>
    private ValueTask<Algorithm> RouteAlgorithmAsync(Algorithm alg, LoadContext context, int depth)
        => _loadBearing.Contains(alg)
            ? ProcessAlgorithmAsync(alg, context, depth)
            : new ValueTask<Algorithm>(ProcessAlgorithm(alg, context, depth));

    /// <summary>MIRROR OF <see cref="RouteAlgorithmAsync"/> for expression children.</summary>
    private ValueTask<Expr> RouteExprAsync(Expr expr, LoadContext context, int depth)
        => _loadBearing.Contains(expr)
            ? ProcessExprAsync(expr, context, depth)
            : new ValueTask<Expr>(ProcessExpr(expr, context, depth));

    // ── Algorithm processing (synchronous walk: load-free subtrees) ──────────

    // The `depth` parameter mirrors the structural preflight's counting exactly (every
    // Expr/Algorithm node is one level; Property is a pass-through membrane), so the
    // cumulative nested-load guard in FetchAndSpliceAsync can judge the LIVE traversal
    // stack — parent frames plus the nested module's own depth — against the measured
    // ceiling. Frame-local by construction: no cleanup is needed on unwind.
    private Algorithm ProcessAlgorithm(Algorithm alg, LoadContext context, int depth)
    {
        ThrowIfInsufficientStack();
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

    /// <summary>
    /// MIRROR OF <see cref="ProcessAlgorithm"/> — keep in lock-step. Runs only on
    /// load-bearing spines (see <see cref="RouteAlgorithmAsync"/>); each child routes
    /// back to the synchronous walk the moment its subtree is load-free.
    /// </summary>
    private async ValueTask<Algorithm> ProcessAlgorithmAsync(Algorithm alg, LoadContext context, int depth)
    {
        ThrowIfInsufficientStack();
        _sourceProcessingCancellationToken.ThrowIfCancellationRequested();

        if (alg is Algorithm.Builtin) return alg;

        var newOpens = new List<Expr>(alg.Opens.Count);
        foreach (var open in alg.Opens)
            newOpens.Add(await RouteExprAsync(open, LoadContext.OpenList, depth + 1).ConfigureAwait(false));

        var newProperties = new List<Property>(alg.Properties.Count);
        foreach (var prop in alg.Properties)
        {
            var processedValue = await RouteAlgorithmAsync(prop.Value, LoadContext.PropertyDef, depth + 1).ConfigureAwait(false);
            // Unwrap only algorithm-valued single-block property bodies, exactly as in
            // the synchronous walk.
            processedValue = processedValue.UnwrapSingleBlockPropertyBody();
            newProperties.Add(prop.WithValue(processedValue));
        }

        var newOutput = new List<Expr>(alg.Output.Count);
        foreach (var expr in alg.Output)
        {
            var outputCtx = context is LoadContext.PropertyDef or LoadContext.OpenList
                ? LoadContext.PropertyDef
                : LoadContext.RuntimeExpr;
            newOutput.Add(await RouteExprAsync(expr, outputCtx, depth + 1).ConfigureAwait(false));
        }

        return alg with
        {
            Opens = newOpens,
            Properties = newProperties,
            Output = newOutput,
        };
    }

    // ── Expression processing (synchronous walk: load-free subtrees) ─────────

    private Expr ProcessExpr(Expr expr, LoadContext context, int depth)
    {
        ThrowIfInsufficientStack();

        if (expr.TryGetUnresolvedLoadArguments(out _))
        {
            // Unreachable by construction: any subtree containing a load call is
            // marked load-bearing and routed through the async twin. Fail loudly
            // rather than fetch on a path that cannot await.
            throw new InvalidOperationException(
                "Internal error: the synchronous module-elaboration walk reached a load call. " +
                "Load-bearing subtrees must route through the async walk.");
        }

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

    /// <summary>
    /// MIRROR OF <see cref="ProcessExpr"/> — keep in lock-step. Runs only on
    /// load-bearing spines; every child routes through <see cref="RouteExprAsync"/> /
    /// <see cref="RouteAlgorithmAsync"/> so load-free children complete inline on the
    /// calibrated synchronous walk. The LINQ projections of the synchronous walk are
    /// explicit loops here because their element rewrites may await.
    /// </summary>
    private async ValueTask<Expr> ProcessExprAsync(Expr expr, LoadContext context, int depth)
    {
        ThrowIfInsufficientStack();

        if (expr.TryGetUnresolvedLoadArguments(out var loadArgs))
            return await ProcessLoadAsync(loadArgs, context, expr.Span, depth).ConfigureAwait(false);

        switch (expr)
        {
            case Expr.Call(var func, var args):
            {
                var newFunc = await RouteExprAsync(func, LoadContext.RuntimeExpr, depth + 1).ConfigureAwait(false);
                var newArgs = new List<Expr>(args.Count);
                foreach (var argExpr in args)
                    newArgs.Add(await RouteExprAsync(argExpr, LoadContext.RuntimeExpr, depth + 1).ConfigureAwait(false));
                return new Expr.Call(newFunc, new OutputBundle(newArgs)) { Span = expr.Span };
            }

            case Expr.AlgorithmExpr(var alg):
                return new Expr.AlgorithmExpr(
                    await RouteAlgorithmAsync(alg, context, depth + 1).ConfigureAwait(false))
                { Span = expr.Span };

            case Expr.Capture(var captureBody):
            {
                var newRows = new List<Expr>(captureBody.Count);
                foreach (var row in captureBody)
                    newRows.Add(await RouteExprAsync(row, context, depth + 1).ConfigureAwait(false));
                return new Expr.Capture(new OutputBundle(newRows)) { Span = expr.Span };
            }

            case Expr.Binary(var op, var left, var right):
                return new Expr.Binary(op,
                    await RouteExprAsync(left, LoadContext.RuntimeExpr, depth + 1).ConfigureAwait(false),
                    await RouteExprAsync(right, LoadContext.RuntimeExpr, depth + 1).ConfigureAwait(false))
                { Span = expr.Span };

            case Expr.Unary(var op, var operand):
                return new Expr.Unary(op,
                    await RouteExprAsync(operand, LoadContext.RuntimeExpr, depth + 1).ConfigureAwait(false))
                { Span = expr.Span };

            case Expr.Index(var target, var selector):
                return new Expr.Index(
                    await RouteExprAsync(target, LoadContext.RuntimeExpr, depth + 1).ConfigureAwait(false),
                    await RouteExprAsync(selector, LoadContext.RuntimeExpr, depth + 1).ConfigureAwait(false))
                { Span = expr.Span };

            case Expr.SequenceSpread(var operand):
                return new Expr.SequenceSpread(
                    await RouteExprAsync(operand, context, depth + 1).ConfigureAwait(false))
                {
                    Span = expr.Span,
                    SpreadMarkerSpan = ((Expr.SequenceSpread)expr).SpreadMarkerSpan,
                };

            case Expr.SequenceConstruct(var left, var right):
                return new Expr.SequenceConstruct(
                    await RouteExprAsync(left, context, depth + 1).ConfigureAwait(false),
                    await RouteExprAsync(right, context, depth + 1).ConfigureAwait(false))
                { Span = expr.Span };

            case Expr.ListLiteral(var items):
            {
                var newItems = new List<Expr>(items.Count);
                foreach (var item in items)
                    newItems.Add(await RouteExprAsync(item, context, depth + 1).ConfigureAwait(false));
                return new Expr.ListLiteral(newItems) { Span = expr.Span };
            }

            case Expr.DotCall dotCall:
            {
                var newTarget = await RouteExprAsync(
                    dotCall.Target, dotCall.Args is null ? context : LoadContext.RuntimeExpr, depth + 1).ConfigureAwait(false);
                OutputBundle? newArgs = null;
                if (dotCall.Args is { } dotArgs)
                {
                    var rewritten = new List<Expr>(dotArgs.Count);
                    foreach (var argExpr in dotArgs)
                        rewritten.Add(await RouteExprAsync(argExpr, LoadContext.RuntimeExpr, depth + 1).ConfigureAwait(false));
                    newArgs = new OutputBundle(rewritten);
                }

                // `with` keeps every stored dot-edge fact intact, as in the
                // synchronous walk.
                return dotCall with { Target = newTarget, Args = newArgs };
            }

            case Expr.Grace grace:
                return grace with
                {
                    Inner = await RouteExprAsync(grace.Inner, context, depth + 1).ConfigureAwait(false),
                };

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

    private async ValueTask<Expr> ProcessLoadAsync(OutputBundle args, LoadContext context, SourceSpan? span, int depth)
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

        // 5. Cache check — an already-elaborated module splices without re-traversal
        // or re-download, so it charges no cumulative traversal depth and never
        // suspends.
        if (_cache.TryGetValue(normalized, out var cached))
            return new Expr.AlgorithmExpr(cached) { Span = span };

        // 6. Fetch + parse + splice — the loader's one awaiting path.
        return await FetchAndSpliceAsync(normalized, span, depth).ConfigureAwait(false);
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
    /// Awaits the remote source code, parses it, runs load elaboration recursively,
    /// and returns an algorithm expression containing the loaded algorithm.
    /// <paramref name="depth"/> is the load site's own traversal depth within the
    /// module currently being processed; together with the traversal levels ancestor
    /// modules hold live it bounds the nested elaboration cumulatively (see
    /// <see cref="MaxTraversalDepth"/>). An incomplete download suspends HERE — the
    /// method resumes after the await with all validation, budget, and splice steps
    /// continuing exactly once; the downloader is never re-invoked for this fetch.
    /// </summary>
    private async ValueTask<Expr> FetchAndSpliceAsync(string normalizedUrl, SourceSpan? span, int depth)
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

            // Fetch. The await is the elaboration's genuine suspension point: an
            // incomplete ValueTask unwinds to the host until the download completes,
            // then processing resumes here exactly once. `catch` around the await
            // uniformly covers a synchronously-throwing downloader and a faulted
            // awaitable.
            string source;
            try
            {
                _sourceProcessingCancellationToken.ThrowIfCancellationRequested();
                source = await _downloadCode(normalizedUrl, _sourceProcessingCancellationToken).ConfigureAwait(false);
                _sourceProcessingCancellationToken.ThrowIfCancellationRequested();
            }
            catch (OperationCanceledException) when (_sourceProcessingCancellationToken.IsCancellationRequested)
            {
                // Host cancellation is authoritative, including TOKEN IDENTITY. The
                // downloader may have faulted with its own timeout/cancellation token
                // while reacting to the host request; normalize that race to the exact
                // configured source-processing token instead of leaking the downloader's.
                _sourceProcessingCancellationToken.ThrowIfCancellationRequested();
                throw; // Unreachable; keeps the compiler's flow analysis explicit.
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

            // Recursively elaborate any load calls in the fetched module. The fetched
            // tree gets its own load-bearing pre-scan so its load-free subtrees take
            // the synchronous walk too.
            _sourceProcessingCancellationToken.ThrowIfCancellationRequested();
            MarkLoadBearing(syntaxResult.SyntaxRoot);
            var previousTraversalBase = _nestedTraversalBase;
            _nestedTraversalBase = traversalBase;
            Algorithm elaborated;
            try
            {
                elaborated = await RouteAlgorithmAsync(syntaxResult.SyntaxRoot, LoadContext.TopLevel, depth: 1)
                    .ConfigureAwait(false);
            }
            finally
            {
                _nestedTraversalBase = previousTraversalBase;
            }

            // Cancellation never commits a partial module. This check also observes cancellation
            // requested during parsing or recursive elaboration before the cache write.
            _sourceProcessingCancellationToken.ThrowIfCancellationRequested();

            // Mark the module root for editor tooling BEFORE caching so cache hits
            // splice the same marked instance: spans inside the module belong to
            // the module's source text, not the loading document's.
            if (elaborated is Algorithm.User moduleRoot)
                elaborated = moduleRoot with { IsModuleElaborated = true };
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

    // ── Stack reserve backstop ──────────────────────────────────────────────

    /// <summary>
    /// Fail-safe net under the structural gates: probes the runtime's conservative
    /// execution-stack reserve at every walk level (both walks — the async twins'
    /// heavier state-machine frames sit ABOVE synchronous subtree walks on the same
    /// stack, so the synchronous walk needs the probe too). It can only stop an
    /// elaboration EARLIER than a physical overflow would, never change one that has
    /// host stack headroom; every composition inside the measured envelope keeps a
    /// reserve far above the probe's threshold at the gated maximum depth. On failure
    /// the walk unwinds via a private control exception (budget frames release
    /// through their <c>finally</c> blocks) and <see cref="ElaborateAsync"/> reports
    /// one structured diagnostic with the established placeholder root.
    /// </summary>
    private static void ThrowIfInsufficientStack()
    {
        if (!RuntimeHelpers.TryEnsureSufficientExecutionStack())
            throw new ModuleElaborationStackException();
    }

    private sealed class ModuleElaborationStackException : Exception;

    // ── Default downloader ──────────────────────────────────────────────────

    /// <summary>
    /// Default asynchronous HTTP downloader using HttpClient. The configured
    /// source-processing token cancels the request; the client's own ten-second
    /// timeout surfaces as an ordinary fetch failure when that token is not
    /// cancelled.
    /// </summary>
    private static async ValueTask<string> DefaultDownloadCode(string url, CancellationToken cancellationToken)
    {
        using var client = new HttpClient();
        client.Timeout = TimeSpan.FromSeconds(10);
        return await client.GetStringAsync(url, cancellationToken).ConfigureAwait(false);
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
