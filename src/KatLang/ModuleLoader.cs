using System.Runtime.CompilerServices;

namespace KatLang;

/// <summary>
/// Elaboration pass that resolves <c>load('url')</c> directives after parsing.
/// Eager regions load before parameter detection; conditional alternatives load on selection.
///
/// <para>
/// <c>load</c> is a source-elaboration directive, NOT a runtime callable.
/// Outside deferred branch regions, load calls are replaced with
/// <see cref="Expr.AlgorithmExpr"/> nodes containing the parsed remote algorithm.
/// A selected deferred region completes loading and front-end elaboration before its body runs.
/// </para>
///
/// <para><b>Async-only module acquisition:</b> source text is obtained through ONE
/// asynchronous contract, <c>Func&lt;string, CancellationToken, ValueTask&lt;string&gt;&gt;</c>,
/// which every constructor REQUIRES — the loader owns no transport and ships no default
/// downloader, so all module bytes (and any transport policy such as redirect handling)
/// come from the host-supplied delegate.
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
/// <para>Security: validates each source-written load target against the configured domain
/// allowlist before handing it to the downloader, and enforces size limits, cycle detection,
/// and optional host cancellation during source/module processing. Redirects and all other
/// transport behavior belong to the host-supplied downloader.</para>
///
/// <para><b>Internal by design (v0.8.188):</b> this is ONE stage of the authoritative
/// front-end pipeline (<see cref="FrontEndPipeline"/>), not a host-composable API —
/// the same boundary rule that internalized <see cref="ParameterDetector"/> and
/// <see cref="ImplicitArgumentResolver"/> in v0.8.187, and this stage is even more
/// incomplete: an <see cref="ElaborateAsync"/>-only tree has had NO parameter
/// detection (a spliced module's declared parameter references are still raw
/// <see cref="Expr.Resolve"/> nodes, so its algorithms cannot bind their arguments),
/// no implicit-argument resolution, and no property-exposure finalization (see
/// <c>FrontEndElaborationBoundaryTests</c>). Hosts get module loading through
/// <see cref="Parser.ParseAsync"/> / <see cref="KatLangEngine.RunAsync"/> with
/// <see cref="RunOptions.DownloadCode"/> and <see cref="RunOptions.AllowedHosts"/> —
/// the complete pipeline, including an in-memory downloader completing
/// synchronously exactly as it would here.</para>
/// </summary>
internal sealed partial class ModuleLoader
{
    private readonly Func<string, CancellationToken, ValueTask<string>> _downloadCode;
    private readonly CancellationToken _sourceProcessingCancellationToken;

    // The token the walks and the downloader observe RIGHT NOW. During initial elaboration it
    // is the configured source-processing token. While a deferred region materializes (under
    // the materialization gate) it is that token LINKED with the requesting materialization's
    // own token: a deferred materialization exists only because evaluation selected a branch,
    // so the requesting evaluation's lifetime cancels its module work — an in-flight download
    // receives the cancellation, the partial module never reaches the cache, and the budget
    // reservations roll back exactly as for host source cancellation (see
    // LoadDeferredRegionAsync). Ordinary eager loads never see anything but the configured
    // token, and the configured token keeps its IDENTITY whenever it is the cancelled one
    // (see ThrowIfCancellationRequested).
    private CancellationToken _cancellationToken;
    private readonly ModuleLoadTarget.AllowedHosts _allowedHosts;

    // Keyed by the CANONICAL module URL (ModuleLoadTarget), as are _inProgress and every
    // downloader request: identity, cycle detection, and transport name one resource.
    private readonly Dictionary<string, CachedModule> _cache = new();
    private readonly HashSet<string> _inProgress = new();
    private readonly DiagnosticBag _diagnostics;

    /// <summary>
    /// One module-cache entry: the caller-independent import view every splice shares, and the
    /// aggregate source its elaboration charged — its own source plus everything its own loads
    /// charged (nested downloads and nested splices). A later splice of the view adds exactly
    /// that much content to the elaborated program, which the front end elaborates once more in
    /// the splice's scope, so a cache hit charges <see cref="Weight"/> (see
    /// <see cref="ProcessLoadAsync"/>).
    /// </summary>
    private readonly record struct CachedModule(Algorithm View, int Weight);

    /// <summary>
    /// The aggregate source charged by the cache-hit splices of ONE walk frame — the root
    /// elaboration, a fetched module's nested elaboration, or a deferred materialization.
    /// Observed host cancellation rolls a frame's ledger back with the frame's own source
    /// reservation, so an abandoned walk leaves only the charges of frames that completed.
    /// </summary>
    private sealed class SpliceLedger
    {
        internal long Charged;
    }

    // The diagnostics bag the walks report into: the elaboration's own bag during
    // ElaborateAsync, and a per-materialization bag while a deferred region is being
    // materialized (LoadDeferredRegionAsync swaps it under the materialization gate), so a
    // demand-time load never appends to a parse result that has already been published.
    private DiagnosticBag _sink;

    // The splice ledger of the walk frame currently running (part of the walk context).
    private SpliceLedger _spliceLedger = new();

    // B2c: materializations are serialized per loader exactly as initial elaboration is one
    // logical sequence — the walk memos, the in-progress module set, and the traversal base
    // are plain fields by that contract. Concurrent selections of one or several deferred
    // branches queue here; a region already materialized by the time its turn comes returns
    // the cached body without any loader work.
    private readonly SemaphoreSlim _materializationGate = new(1, 1);

    /// <summary>Deferred module regions this loader created during its most recent walk (test-observable).</summary>
    internal int DeferredRegionCount { get; private set; }

    /// <summary>The configured host source-processing token — the authoritative cancellation identity.</summary>
    internal CancellationToken SourceProcessingCancellationToken => _sourceProcessingCancellationToken;

    /// <summary>
    /// The ONE cancellation observation of the loader's walks and fetches. The configured
    /// source-processing token is checked FIRST so that whenever the host cancelled source
    /// processing the thrown exception carries exactly that token (the established identity
    /// contract), and only then the active token — which additionally carries a deferred
    /// materialization's own cancellation while one is in flight.
    /// </summary>
    private void ThrowIfCancellationRequested()
    {
        _sourceProcessingCancellationToken.ThrowIfCancellationRequested();
        _cancellationToken.ThrowIfCancellationRequested();
    }

    private bool IsCancellationRequested
        => _sourceProcessingCancellationToken.IsCancellationRequested || _cancellationToken.IsCancellationRequested;

    /// <summary>The per-loader materialization gate (see <see cref="DeferredModuleRegion.MaterializeAsync"/>).</summary>
    internal SemaphoreSlim MaterializationGate => _materializationGate;

    // Reference-identity set of nodes with an unresolved load call at or beneath them —
    // the load-bearing spines. Populated by MarkLoadBearing before each tree is walked
    // (the root in ElaborateAsync, each fetched module in FetchAndSpliceAsync); RouteExprAsync /
    // RouteAlgorithmAsync consult it to decide sync vs async processing per child. Marking is
    // path-complete: every node from which the rewrite walk can reach a load is marked, so the
    // synchronous walk (entered only at unmarked nodes) can never encounter a load.
    // The set is cleared at the loader's elaboration boundary so a reusable loader does
    // not retain every caller-owned input tree for the rest of its lifetime.
    private readonly HashSet<object> _loadBearing = new(ReferenceEqualityComparer.Instance);

    // DAG-safety memos of the rewrite walks. Load-free synchronous subtrees are keyed by
    // LoadContext alone. Load-bearing async-spine nodes additionally key by their effective
    // live traversal depth (`_nestedTraversalBase + depth`): a near-ceiling load can be rejected
    // before fetch while the SAME node reached on a shallower path is admissible, so reusing the
    // rejection across depths would change the pre-memo tree behavior. Routing is per-node
    // deterministic, and an entry is stored only AFTER the node's processing fully completed
    // (an async twin that suspends mid-node can never expose a partially processed node as done).
    // A shared load
    // CALL node is thereby processed once per constant (node, context, live-depth) region — one
    // budget charge, diagnostic, and splice there — while a genuinely depth-sensitive second
    // occurrence is rewritten independently. Distinct load nodes remain independent load sites.
    // Lazily allocated and cleared with _loadBearing at the loader's elaboration boundary; the
    // loader processes one logical elaboration sequentially, so plain fields suffice.
    private readonly Dictionary<Expr, Expr>?[] _exprWalkMemos = new Dictionary<Expr, Expr>?[4];
    private readonly Dictionary<Algorithm, Algorithm>?[] _algorithmWalkMemos = new Dictionary<Algorithm, Algorithm>?[4];
    private readonly Dictionary<Expr, Dictionary<int, Expr>>?[] _loadBearingExprWalkMemos =
        new Dictionary<Expr, Dictionary<int, Expr>>?[4];
    private readonly Dictionary<Algorithm, Dictionary<int, Algorithm>>?[] _loadBearingAlgorithmWalkMemos =
        new Dictionary<Algorithm, Dictionary<int, Algorithm>>?[4];

    /// <summary>
    /// Passive test-only traversal observer (see <see cref="FrontEndTraversalObservations"/>);
    /// null in production. Set before <see cref="ElaborateAsync"/> by measuring callers.
    /// </summary>
    internal FrontEndTraversalObservations? TraversalObservations { get; set; }

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
    /// traversal call through a <see cref="WalkContextScope"/>, so downloader failures,
    /// cancellation, and nested rejections can never leak or corrupt it. Cache hits
    /// splice without re-traversal and charge nothing. The loader processes one
    /// logical elaboration sequentially (a suspension resumes the same walk, never a
    /// parallel one), so this stays a plain field across await boundaries.
    /// </summary>
    private int _nestedTraversalBase;

    /// <summary>
    /// The IMPORT SITE of the module content the walk is currently inside: the span, in
    /// the CURRENT document, of the load directive through which that content was demanded
    /// (the outermost one for a chain of nested loads), or null while the walk is over the
    /// document's own text. Module content carries no source locations of its own (see
    /// <see cref="ToImportView"/>), so every diagnostic the loader raises for a load written
    /// INSIDE a module — a failed fetch, a cycle, a policy rejection, a nested parse failure —
    /// is positioned here, at the site the current document wrote; a load written in the
    /// document keeps its own span. Part of the swappable walk context: a deferred region
    /// records the site its body was reached under and its materialization restores it.
    /// </summary>
    private SourceSpan? _importSite;
    private StateScopeStack _walkContextScopes;

    /// <summary>
    /// The loader's swappable WALK CONTEXT: the five fields a nested walk temporarily
    /// changes — the diagnostics bag (<see cref="_sink"/>), the live traversal base
    /// (<see cref="_nestedTraversalBase"/>), the active cancellation token
    /// (<see cref="_cancellationToken"/>), the import site (<see cref="_importSite"/>), and the
    /// frame's splice ledger (<see cref="_spliceLedger"/>).
    /// Constructing the scope captures the current values; the entry helper then installs
    /// the temporary ones; <see cref="Dispose"/>
    /// restores exactly the captured values — always from a <c>using</c>, so restoration
    /// runs on the ordinary return, on a structured rejection, on cancellation, and on a
    /// downloader exception alike, and no field can be left pointing at a finished walk's
    /// sink, base, token, or ledger. Scopes nest (a nested module load inside a deferred
    /// materialization): each restores what it displaced, in reverse order of entry. The
    /// default value installed nothing and restores nothing.
    /// </summary>
    private readonly struct WalkContextScope : IDisposable
    {
        private readonly ModuleLoader? _loader;
        private readonly DiagnosticBag _sink;
        private readonly int _nestedTraversalBase;
        private readonly CancellationToken _cancellationToken;
        private readonly SourceSpan? _importSite;
        private readonly SpliceLedger _spliceLedger;
        private readonly StateScopeStack.Ticket _ticket;

        /// <summary>Captures <paramref name="loader"/>'s current walk context.</summary>
        internal WalkContextScope(ModuleLoader loader)
        {
            _loader = loader;
            _sink = loader._sink;
            _nestedTraversalBase = loader._nestedTraversalBase;
            _cancellationToken = loader._cancellationToken;
            _importSite = loader._importSite;
            _spliceLedger = loader._spliceLedger;
            _ticket = loader._walkContextScopes.Enter();
        }

        public void Dispose()
        {
            if (_loader is null)
                return;

            _loader._walkContextScopes.Exit(_ticket);
            _loader._spliceLedger = _spliceLedger;
            _loader._importSite = _importSite;
            _loader._cancellationToken = _cancellationToken;
            _loader._nestedTraversalBase = _nestedTraversalBase;
            _loader._sink = _sink;
        }
    }

    /// <summary>
    /// Enters the walk context of a deferred-region materialization
    /// (<see cref="LoadDeferredRegionAsync"/>): diagnostics go to the materialization's own
    /// bag, traversal depth is judged from the base the eager walk recorded for the
    /// region, loads inside the body are positioned at the import site the eager walk
    /// recorded for it, every walk check and the downloader observe the linked token, and the
    /// body's cache-hit splices charge the materialization's own ledger.
    /// </summary>
    private WalkContextScope EnterMaterializationContext(
        DiagnosticBag sink,
        int nestedTraversalBase,
        SourceSpan? importSite,
        SpliceLedger spliceLedger,
        CancellationToken cancellationToken)
    {
        var scope = new WalkContextScope(this);
        _sink = sink;
        _nestedTraversalBase = nestedTraversalBase;
        _importSite = importSite;
        _cancellationToken = cancellationToken;
        _spliceLedger = spliceLedger;
        return scope;
    }

    /// <summary>
    /// Enters the walk context of a fetched nested module's elaboration: the live
    /// traversal base and the import site change (every load written inside the module is
    /// positioned at the site the current document wrote for it), and the module's own
    /// cache-hit splices charge its own ledger; the bag and the token stay those of the
    /// enclosing walk.
    /// </summary>
    private WalkContextScope EnterNestedTraversal(int nestedTraversalBase, SourceSpan? importSite, SpliceLedger spliceLedger)
    {
        var scope = new WalkContextScope(this);
        _nestedTraversalBase = nestedTraversalBase;
        _importSite = importSite;
        _spliceLedger = spliceLedger;
        return scope;
    }

    /// <summary>Run-local state exposed internally for cleanup-invariant regression tests.</summary>
    internal int InProgressModuleCount => _inProgress.Count;

    /// <summary>Run-local state exposed internally for cache-commit regression tests.</summary>
    internal int CachedModuleCount => _cache.Count;

    /// <summary>
    /// The walk context (<see cref="WalkContextScope"/>) exposed internally for scope-restoration
    /// regression tests: the sink by identity, the live traversal base, the active token, the
    /// import site, and the splice ledger by identity.
    /// </summary>
    internal (object Sink, int NestedTraversalBase, CancellationToken CancellationToken, SourceSpan? ImportSite, object SpliceLedger) WalkContext
        => (_sink, _nestedTraversalBase, _cancellationToken, _importSite, _spliceLedger);

    /// <summary>
    /// A fresh diagnostic bag for one demand-time materialization of a region this loader
    /// deferred, bounded by the run's configured diagnostic count: each materialization is its
    /// own operation with its own list (see <see cref="SourceProcessingBudget.CreateDiagnosticBag"/>).
    /// </summary>
    internal DiagnosticBag CreateDiagnosticBag() => _budget.CreateDiagnosticBag();

    /// <summary>
    /// Creates a new ModuleLoader.
    /// </summary>
    /// <param name="diagnostics">The operation's diagnostic bag, shared with the parser.</param>
    /// <param name="downloadCode">
    /// Required host-supplied asynchronous code fetcher: URL and the configured
    /// <paramref name="sourceProcessingCancellationToken"/> → source text. A host with the
    /// source already in memory returns <c>ValueTask.FromResult(text)</c> and the whole
    /// elaboration completes synchronously. The loader owns no transport of its own —
    /// there is no default downloader, so all fetch behavior, including any redirect
    /// policy, belongs to this delegate.
    /// </param>
    /// <param name="allowedHosts">
    /// Set of allowed hosts (exact match or subdomain, compared in canonical IDNA form — see
    /// <see cref="ModuleLoadTarget"/>). Defaults to katlang.org only. The public options
    /// boundary (<see cref="FrontEndPipeline.NormalizeAllowedHosts"/>) trims entries and rejects
    /// blank ones before a loader exists; a blank or otherwise unusable entry that reaches a
    /// directly constructed loader admits nothing (<see cref="ModuleLoadTarget.AllowedHosts"/>).
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
        DiagnosticBag diagnostics,
        Func<string, CancellationToken, ValueTask<string>> downloadCode,
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
    /// The AST-based convenience constructor above delegates here with a fresh default budget, so a
    /// directly-constructed loader still enforces the always-active ceilings.
    /// </summary>
    internal ModuleLoader(
        DiagnosticBag diagnostics,
        Func<string, CancellationToken, ValueTask<string>> downloadCode,
        IEnumerable<string>? allowedHosts,
        SourceProcessingBudget? budget,
        CancellationToken sourceProcessingCancellationToken)
    {
        // No transport is ever substituted: a loader without a real downloader cannot
        // exist, so no module-loading network request can originate from KatLang itself.
        ArgumentNullException.ThrowIfNull(downloadCode);

        _diagnostics = diagnostics;
        _sink = diagnostics;
        _downloadCode = downloadCode;
        _sourceProcessingCancellationToken = sourceProcessingCancellationToken;
        _cancellationToken = sourceProcessingCancellationToken;
        _allowedHosts = ModuleLoadTarget.AllowedHosts.From(allowedHosts);
        _budget = budget ?? new SourceProcessingBudget(null);
    }

    // ── Loader entry points ──────────────────────────────────────────────────

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
    ///
    /// <para><b>Shared subtrees (acyclic DAGs) are legal and DAG-safe:</b> the pre-scan
    /// and both rewrite walks are reference-identity memoized per elaboration, so work is
    /// bounded by distinct reachable (node, context) states for load-free regions and distinct
    /// reachable (node, context, live-depth) states on load-bearing spines — never by blindly
    /// expanding every root-to-node path. Rewritten output preserves the input's sharing whenever
    /// its rewrite context is the same. A load call node referenced several times at the same
    /// context and live depth is ONE load site (processed, budget-charged, diagnosed, and spliced
    /// once). LoadContext or
    /// near-ceiling live-depth differences intentionally split the rewrite because they can change
    /// validity; two distinct load nodes likewise remain two sites even when they name the same URL
    /// (which the per-URL module cache already downloads only once).</para>
    /// </summary>
    /// <exception cref="OperationCanceledException">
    /// The configured source-processing token was cancelled. Delivered through the returned
    /// task once the elaboration has started awaiting.
    /// </exception>
    public async ValueTask<Algorithm> ElaborateAsync(Algorithm root)
    {
        ThrowIfCancellationRequested();
        // The root walk is one frame: its cache-hit splices charge this ledger, released if
        // observed cancellation abandons the walk (see SpliceLedger).
        var rootLedger = new SpliceLedger();
        var enclosingLedger = _spliceLedger;
        _spliceLedger = rootLedger;
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

            ThrowIfCancellationRequested();

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
        catch (OperationCanceledException) when (IsCancellationRequested)
        {
            // The abandoned walk keeps no splice: release what its own splices charged.
            _budget.RollbackAggregate(rootLedger.Charged);
            throw;
        }
        finally
        {
            _spliceLedger = enclosingLedger;
            _loadBearing.Clear();
            Array.Clear(_exprWalkMemos);
            Array.Clear(_algorithmWalkMemos);
            Array.Clear(_loadBearingExprWalkMemos);
            Array.Clear(_loadBearingAlgorithmWalkMemos);
        }
    }

    // ── Context tracking ────────────────────────────────────────────────────

    /// <summary>
    /// Tracks where a load call appears to enforce position restrictions.
    /// </summary>
    internal enum LoadContext
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
    /// visits patterns and stored fallback identities the rewrite walk leaves
    /// untouched, and it descends every conditional branch body while the rewrite
    /// walks defer load-bearing ones), so an UNMARKED node is proof its subtree
    /// elaborates without ever needing to await, and a MARKED branch body is exactly
    /// one that <see cref="DeferOrKeepBranches"/> must defer.
    ///
    /// <para><b>DAG-safety:</b> the scan is reference-identity memoized per call. A
    /// completed node's marked-ness is exactly "its subtree reaches a load", so a
    /// later reach of the same node object descends nothing: it marks the CURRENT
    /// root-path (stopping at the first already-marked ancestor) when the node is
    /// marked, and skips otherwise — every node from which a load is reachable still
    /// ends up marked, with total work bounded by the distinct nodes and edges rather
    /// than the number of root-to-node paths.</para>
    /// </summary>
    private void MarkLoadBearing(Algorithm root)
        => new LoadBearingMarker(_loadBearing, TraversalObservations).VisitAlgorithm(root);

    private sealed class LoadBearingMarker(
        HashSet<object> marked,
        FrontEndTraversalObservations? observations) : AstWalker
    {
        private readonly List<object> _path = [];

        // Completion-marked visited set: a node is added only after its subtree scan
        // finished, so its marked-ness is final whenever a later reach consults it
        // (the graph is acyclic — preflight-gated — so a re-reach during the node's
        // own scan is impossible).
        private readonly HashSet<object> _visited = new(ReferenceEqualityComparer.Instance);

        protected override bool VisitsExplicitParameterDeclarations => false;

        public override void VisitAlgorithm(Algorithm algorithm)
        {
            // The scan recurses the same depths the walks do (small walker frames,
            // preflight-gated), so it carries the same reserve backstop — on a host
            // thread below the documented envelope the scan must fail structured,
            // not by overflowing before the walk even starts.
            ThrowIfInsufficientStack();
            if (_visited.Contains(algorithm))
            {
                if (marked.Contains(algorithm))
                    MarkCurrentPath();
                return;
            }

            observations?.RecordLoaderMarkerExpansion();
            _path.Add(algorithm);
            try
            {
                base.VisitAlgorithm(algorithm);
            }
            finally
            {
                _path.RemoveAt(_path.Count - 1);
            }

            _visited.Add(algorithm);
        }

        public override void VisitExpr(Expr expr)
        {
            ThrowIfInsufficientStack();
            if (_visited.Contains(expr))
            {
                if (marked.Contains(expr))
                    MarkCurrentPath();
                return;
            }

            if (expr.TryGetUnresolvedLoadArguments(out _))
            {
                // Mark the load call and its live root-path; elaboration replaces the
                // whole call, so its argument slots are never walked. The upward stop
                // at the first already-marked node keeps repeated loads cheap.
                marked.Add(expr);
                MarkCurrentPath();
                _visited.Add(expr);
                return;
            }

            observations?.RecordLoaderMarkerExpansion();
            _path.Add(expr);
            try
            {
                base.VisitExpr(expr);
            }
            finally
            {
                _path.RemoveAt(_path.Count - 1);
            }

            _visited.Add(expr);
        }

        private void MarkCurrentPath()
        {
            for (var i = _path.Count - 1; i >= 0; i--)
            {
                if (!marked.Add(_path[i]))
                    break;
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
            // Clause families dispatch HERE, before any state machine is entered, to their
            // own twin: the ordinary-body twin keeps exactly its calibrated await sites and
            // frame, and a family level still costs one state-machine frame.
            ? alg is Algorithm.Conditional conditional
                ? ProcessConditionalAlgorithmAsync(conditional, context, depth)
                : ProcessAlgorithmAsync(alg, context, depth)
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
    //
    // DAG-safety memo checks live INSIDE this frame (and the twins'), never in a wrapper:
    // an extra method (or async state machine) per recursion level would change the
    // calibrated one-frame-per-level stack shape this walk's measured envelope rests on.
    private Algorithm ProcessAlgorithm(Algorithm alg, LoadContext context, int depth)
    {
        ThrowIfInsufficientStack();
        ThrowIfCancellationRequested();

        if (alg is Algorithm.Builtin) return alg;

        var memo = _algorithmWalkMemos[(int)context] ??= new(ReferenceEqualityComparer.Instance);
        if (memo.TryGetValue(alg, out var memoized))
            return memoized;

        TraversalObservations?.RecordLoaderWalkExpansion();

        Algorithm result;
        if (alg is Algorithm.Conditional conditional)
        {
            // A clause family (B2c): its family-owned open list (host trees only — parsed
            // families keep their opens on the branch bodies) is SHARED by every alternative
            // and is processed eagerly like any open list, while each alternative branch body
            // is a deferred module-elaboration region — see DeferOrKeepBranches. On this
            // synchronous walk the family is load-free, so every branch is simply kept.
            var newFamilyOpens = new List<Expr>(conditional.Opens.Count);
            foreach (var open in conditional.Opens)
                newFamilyOpens.Add(ProcessExpr(open, LoadContext.OpenList, depth + 1));

            result = conditional with
            {
                Opens = newFamilyOpens,
                Branches = DeferOrKeepBranches(conditional, context, depth),
            };
        }
        else if (alg is Algorithm.User user)
        {
            var newOpens = new List<Expr>(user.Opens.Count);
            foreach (var open in user.Opens)
                newOpens.Add(ProcessExpr(open, LoadContext.OpenList, depth + 1));

            var newProperties = new List<Property>(user.Properties.Count);
            foreach (var prop in user.Properties)
            {
                var processedValue = ProcessAlgorithm(prop.Value, LoadContext.PropertyDef, depth + 1);
                // Unwrap only algorithm-valued single-block property bodies. A plain
                // sequence value such as (a, b) stays one captured value boundary,
                // while load-elaborated modules become direct property values.
                processedValue = processedValue.UnwrapSingleBlockPropertyBody();
                newProperties.Add(prop.WithValue(processedValue));
            }

            var newOutput = new List<Expr>(user.Output.Count);
            foreach (var expr in user.Output)
            {
                // In a property definition or open list body, output is allowed for load
                // At top-level, output is runtime
                var outputCtx = context is LoadContext.PropertyDef or LoadContext.OpenList
                    ? LoadContext.PropertyDef
                    : LoadContext.RuntimeExpr;
                newOutput.Add(ProcessExpr(expr, outputCtx, depth + 1));
            }

            result = user with
            {
                Opens = newOpens,
                Properties = newProperties,
                Output = newOutput,
            };
        }
        else
        {
            // The closed hierarchy has exactly three variants and the builtin returned above.
            throw new InvalidOperationException($"Unhandled algorithm variant: {alg.GetType().Name}");
        }

        memo[alg] = result;
        return result;
    }

    /// <summary>
    /// MIRROR OF the ordinary-body part of <see cref="ProcessAlgorithm"/> — keep in
    /// lock-step (clause families: <see cref="ProcessConditionalAlgorithmAsync"/>). Runs
    /// only on load-bearing spines (see <see cref="RouteAlgorithmAsync"/>); each child
    /// routes back to the synchronous walk the moment its subtree is load-free. The memo
    /// entry is stored only after the (possibly suspending) processing fully completed,
    /// from INSIDE this one state machine — no wrapper frame may join the recursion spine.
    /// </summary>
    private async ValueTask<Algorithm> ProcessAlgorithmAsync(Algorithm alg, LoadContext context, int depth)
    {
        ThrowIfInsufficientStack();
        ThrowIfCancellationRequested();

        if (alg is Algorithm.Builtin) return alg;

        if (alg is not Algorithm.User user)
        {
            // Unreachable by construction: RouteAlgorithmAsync dispatches families to their
            // own twin (the builtin returned above). Fail loudly rather than rewrite a family
            // through the ordinary-body accessors, which are empty for it (the original
            // traversal gap).
            throw new InvalidOperationException(
                "Internal error: the ordinary-body async module-elaboration walk reached a clause family. " +
                "Families route through ProcessConditionalAlgorithmAsync.");
        }

        var memo = _loadBearingAlgorithmWalkMemos[(int)context] ??=
            new(ReferenceEqualityComparer.Instance);
        if (!memo.TryGetValue(alg, out var rewritesByDepth))
        {
            rewritesByDepth = [];
            memo[alg] = rewritesByDepth;
        }

        var effectiveDepth = checked(_nestedTraversalBase + depth);
        if (rewritesByDepth.TryGetValue(effectiveDepth, out var memoized))
            return memoized;

        TraversalObservations?.RecordLoaderWalkExpansion();

        var newOpens = new List<Expr>(user.Opens.Count);
        foreach (var open in user.Opens)
            newOpens.Add(await RouteExprAsync(open, LoadContext.OpenList, depth + 1).ConfigureAwait(false));

        var newProperties = new List<Property>(user.Properties.Count);
        foreach (var prop in user.Properties)
        {
            var processedValue = await RouteAlgorithmAsync(prop.Value, LoadContext.PropertyDef, depth + 1).ConfigureAwait(false);
            // Unwrap only algorithm-valued single-block property bodies, exactly as in
            // the synchronous walk.
            processedValue = processedValue.UnwrapSingleBlockPropertyBody();
            newProperties.Add(prop.WithValue(processedValue));
        }

        var newOutput = new List<Expr>(user.Output.Count);
        foreach (var expr in user.Output)
        {
            var outputCtx = context is LoadContext.PropertyDef or LoadContext.OpenList
                ? LoadContext.PropertyDef
                : LoadContext.RuntimeExpr;
            newOutput.Add(await RouteExprAsync(expr, outputCtx, depth + 1).ConfigureAwait(false));
        }

        var result = user with
        {
            Opens = newOpens,
            Properties = newProperties,
            Output = newOutput,
        };

        rewritesByDepth[effectiveDepth] = result;
        return result;
    }

    /// <summary>
    /// MIRROR OF the clause-family arm of <see cref="ProcessAlgorithm"/> — keep in lock-step.
    /// A separate twin rather than an arm inside <see cref="ProcessAlgorithmAsync"/> so the
    /// ordinary-body twin keeps exactly its calibrated await sites and frame; a family level
    /// still costs one state-machine frame because <see cref="RouteAlgorithmAsync"/> dispatches
    /// here before any state machine is entered. Same memo discipline as the ordinary twin:
    /// keyed by context and effective live depth, stored only after completion. Only the
    /// family-owned opens can await here: branch bodies are deferred, never descended
    /// (<see cref="DeferOrKeepBranches"/>).
    /// </summary>
    private async ValueTask<Algorithm> ProcessConditionalAlgorithmAsync(
        Algorithm.Conditional conditional, LoadContext context, int depth)
    {
        ThrowIfInsufficientStack();
        ThrowIfCancellationRequested();

        var memo = _loadBearingAlgorithmWalkMemos[(int)context] ??=
            new(ReferenceEqualityComparer.Instance);
        if (!memo.TryGetValue(conditional, out var rewritesByDepth))
        {
            rewritesByDepth = [];
            memo[conditional] = rewritesByDepth;
        }

        var effectiveDepth = checked(_nestedTraversalBase + depth);
        if (rewritesByDepth.TryGetValue(effectiveDepth, out var memoized))
            return memoized;

        TraversalObservations?.RecordLoaderWalkExpansion();

        var newFamilyOpens = new List<Expr>(conditional.Opens.Count);
        foreach (var open in conditional.Opens)
            newFamilyOpens.Add(await RouteExprAsync(open, LoadContext.OpenList, depth + 1).ConfigureAwait(false));

        var result = conditional with
        {
            Opens = newFamilyOpens,
            Branches = DeferOrKeepBranches(conditional, context, depth),
        };
        rewritesByDepth[effectiveDepth] = result;
        return result;
    }

    // ── B2c: deferred module regions ────────────────────────────────────────

    /// <summary>
    /// The ONE owner of branch-lazy module loading's initial-elaboration rule, shared by both
    /// family walks. A branch body that the load-bearing pre-scan proved to contain no
    /// unresolved load is kept exactly as written (there is nothing to elaborate and the eager
    /// front end elaborates it in full). A LOAD-BEARING branch body is not descended: it
    /// becomes a deferred module-elaboration region — nothing under it is fetched, parsed,
    /// elaborated, or budget-charged until evaluation selects that branch — represented in
    /// the output tree by a fresh placeholder object (a shallow clone of the raw body, so the
    /// family keeps its written branch shape and output arity) that CARRIES its region
    /// (<see cref="Algorithm.DeferredRegion"/>) with this walk's context: the family's load
    /// context (the body inherits it exactly as eager elaboration would), the body's counted
    /// depth (<c>CondBranch</c> is a depth membrane, so one level below the family), and the
    /// live traversal base. A fresh placeholder per branch OCCURRENCE keeps regions distinct
    /// even when host branches share one raw body object (the clones share that body's
    /// declaration identity; region identity is the placeholder's own). A body that is itself
    /// a placeholder of an earlier elaboration is deferred over its region-free copy, so the
    /// earlier region can never surface through a materialization of this one.
    /// </summary>
    private IReadOnlyList<CondBranch> DeferOrKeepBranches(Algorithm.Conditional conditional, LoadContext context, int depth)
    {
        var branches = new List<CondBranch>(conditional.Branches.Count);
        foreach (var branch in conditional.Branches)
        {
            if (!_loadBearing.Contains(branch.Body))
            {
                branches.Add(branch);
                continue;
            }

            var rawBody = branch.Body.DeferredRegion is null ? branch.Body : branch.Body with { DeferredRegion = null };
            var placeholder = rawBody with
            {
                DeferredRegion = new DeferredModuleRegion(this, rawBody, context, depth + 1, _nestedTraversalBase, _importSite),
            };
            DeferredRegionCount++;
            branches.Add(branch with { Body = placeholder });
        }

        return branches;
    }

    /// <summary>
    /// The loader half of materializing a deferred region (called by
    /// <see cref="DeferredModuleRegion.MaterializeAsync"/> under this loader's
    /// <see cref="MaterializationGate"/>): the region's raw body is walked exactly like a
    /// subtree of the initial elaboration — its own pre-scan, the routed sync/async walks,
    /// the same per-URL cache, cycle detection, policy checks, and budgets, judged at the
    /// depth and live traversal base the eager walk recorded — with diagnostics reported into
    /// <paramref name="diagnostics"/> rather than the published parse result. Nested clause
    /// families inside the body are deferred again by the same rule. The composed body is
    /// then re-gated at both structural ceilings the eager pipeline applies (the raw-syntax
    /// cap after splicing and the elaboration ceiling), against the allowance left at the
    /// region's depth, and checked for unresolved loads outside nested deferred regions.
    /// The walk memos and the load-bearing set are cleared afterwards, as at the
    /// elaboration boundary.
    ///
    /// <para><paramref name="materializationCancellationToken"/> is the requesting
    /// materialization's own token (cancelled once no evaluation needs the region any more —
    /// see <see cref="DeferredModuleRegion.MaterializeAsync"/>). For the duration of this
    /// load it is LINKED with the configured source-processing token into the active token
    /// every walk check and the downloader observe, so an in-flight download is cancelled
    /// with the evaluation, nothing partial reaches the module cache, and aggregate-source
    /// reservations roll back (download attempts stay charged); the linked source is disposed on the way out, so no
    /// registration outlives the load. Cancellation identity: the configured
    /// source-processing token whenever it is the cancelled one, otherwise the linked token
    /// (the region maps that to the requesting evaluation's own token).</para>
    /// </summary>
    internal async ValueTask<Algorithm> LoadDeferredRegionAsync(
        DeferredModuleRegion region,
        DiagnosticBag diagnostics,
        CancellationToken materializationCancellationToken)
    {
        ThrowIfCancellationRequested();
        materializationCancellationToken.ThrowIfCancellationRequested();

        using var linkedCancellation = CancellationTokenSource.CreateLinkedTokenSource(
            _sourceProcessingCancellationToken,
            materializationCancellationToken);
        // The materialization's cache-hit splices charge its own ledger, released if observed
        // cancellation abandons it, so a cancelled selection can be retried without draining
        // the aggregate (download attempts stay charged).
        var materializationLedger = new SpliceLedger();
        try
        {
            // Restore the walk context before clearing the walk memos, and before disposing
            // the linked source, preserving the original unwind order.
            using var materialization = EnterMaterializationContext(
                diagnostics, region.NestedTraversalBase, region.ImportSite, materializationLedger, linkedCancellation.Token);
            Algorithm loaded;
            try
            {
                MarkLoadBearing(region.RawBody);
                loaded = await RouteAlgorithmAsync(region.RawBody, region.Context, region.Depth).ConfigureAwait(false);
            }
            catch (ModuleElaborationStackException)
            {
                ReportSourceProcessingDiagnostic(
                    SourceProcessingDiagnostics.ModuleElaborationStackExhausted(MaxTraversalDepth));
                return region.RawBody;
            }

            ThrowIfCancellationRequested();

            if (AstStructuralPreflight.Check(
                    loaded,
                    MaxTraversalDepth - region.Depth,
                    AstConsumerProfile.FullyRecursive) is { } compositionRejection)
            {
                ReportSourceProcessingDiagnostic(AstStructuralPreflight.ToParseDiagnostic(
                    compositionRejection, MaxTraversalDepth, _importSite));
                return loaded;
            }

            if (AstStructuralPreflight.Check(
                    loaded,
                    EvaluationLimits.MaxSupportedAstDepth - region.Depth,
                    AstConsumerProfile.FullyRecursive) is { } elaborationRejection)
            {
                _sink.Add(AstStructuralPreflight.ToParseDiagnostic(
                    elaborationRejection, EvaluationLimits.MaxSupportedAstDepth, _importSite));
                return loaded;
            }

            if (LoadElaborationGuard.TryFindFirstUnresolvedLoad(loaded, out _))
                _sink.Add(LoadElaborationGuard.CreatePostElaborationInvariantDiagnostic(loaded, _importSite));

            return loaded;
        }
        catch (OperationCanceledException) when (IsCancellationRequested || linkedCancellation.IsCancellationRequested)
        {
            _budget.RollbackAggregate(materializationLedger.Charged);
            throw;
        }
        finally
        {
            // As at the elaboration boundary: the walk memos and the load-bearing set never
            // outlive one walk. The scope has already restored the enclosing walk context.
            _loadBearing.Clear();
            Array.Clear(_exprWalkMemos);
            Array.Clear(_algorithmWalkMemos);
            Array.Clear(_loadBearingExprWalkMemos);
            Array.Clear(_loadBearingAlgorithmWalkMemos);
        }
    }

    // ── Expression processing (synchronous walk: load-free subtrees) ─────────

    // The DAG-safety memo check lives INSIDE this frame (see ProcessAlgorithm's note): the
    // switch assigns `result` instead of returning so the memo store shares the one
    // calibrated frame per level.
    /// <summary>
    /// The comparison-chain arm of <see cref="ProcessExpr"/>, kept out of that calibrated
    /// frame: the first operand and every link operand are runtime expressions rewritten
    /// one level down, the link list keeping its instance when no operand changed.
    /// </summary>
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)]
    private Expr ProcessComparison(Expr.Comparison comparison, int depth)
    {
        var first = ProcessExpr(comparison.First, LoadContext.RuntimeExpr, depth + 1);
        var links = AstHelpers.RewriteComparisonLinks(
            comparison.Links,
            operand => ProcessExpr(operand, LoadContext.RuntimeExpr, depth + 1));
        return comparison with { First = first, Links = links };
    }

    /// <summary>
    /// MIRROR OF <see cref="ProcessComparison"/> for the async walk (the link loop awaits,
    /// so it lives in its own state machine rather than enlarging
    /// <see cref="ProcessExprAsync"/>'s calibrated frame); like the synchronous helper it
    /// keeps the link list instance when no operand changed.
    /// </summary>
    private async ValueTask<Expr> RouteComparisonAsync(Expr.Comparison comparison, int depth)
    {
        var first = await RouteExprAsync(comparison.First, LoadContext.RuntimeExpr, depth + 1).ConfigureAwait(false);
        List<ComparisonLink>? rewritten = null;
        var links = comparison.Links;
        for (var index = 0; index < links.Count; index++)
        {
            var link = links[index];
            var operand = await RouteExprAsync(link.Operand, LoadContext.RuntimeExpr, depth + 1).ConfigureAwait(false);
            if (rewritten is null && !ReferenceEquals(operand, link.Operand))
            {
                rewritten = new List<ComparisonLink>(links.Count);
                for (var copied = 0; copied < index; copied++)
                    rewritten.Add(links[copied]);
            }

            rewritten?.Add(ReferenceEquals(operand, link.Operand) ? link : link with { Operand = operand });
        }

        return comparison with { First = first, Links = rewritten ?? links };
    }

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

        // Childless leaves skip the memo: they rewrite to themselves in O(1) and can never
        // multiply traversal paths.
        Dictionary<Expr, Expr>? memo = null;
        if (AstTraversalDagSafety.HasTraversableExprChildren(expr))
        {
            memo = _exprWalkMemos[(int)context] ??= new(ReferenceEqualityComparer.Instance);
            if (memo.TryGetValue(expr, out var memoized))
                return memoized;

            TraversalObservations?.RecordLoaderWalkExpansion();
        }

        // Compiler-exhaustive over the closed Expr hierarchy: a new variant is a build
        // error here until it is classified (recursive rewrite or leaf). Keep this switch
        // and the async twin below in lock-step — the twin's statement form keeps a
        // runtime guard instead.
        //
        // Every rewrite is a `with` copy of the node: the record copy carries the node's
        // source span (and every other stored init-only fact) inside the copy constructor,
        // so this calibrated recursion frame holds NO span temporaries of its own. A
        // `new Node(...) { Span = expr.Span }` per arm would give each arm a hidden
        // return buffer and a copy of the 20-byte nullable span in THIS frame — enough,
        // in Debug builds, to push the synchronous walk's 1 MiB envelope below the gated
        // MaxTraversalDepth (measured while converting SourceSpan to a value type).
        Expr result = expr switch
        {
            Expr.Call call => call with
            {
                Function = ProcessExpr(call.Function, LoadContext.RuntimeExpr, depth + 1),
                Args = new OutputBundle(call.Args.Select(argExpr => ProcessExpr(argExpr, LoadContext.RuntimeExpr, depth + 1)).ToList()),
            },

            Expr.AlgorithmExpr block => block with { Algorithm = ProcessAlgorithm(block.Algorithm, context, depth + 1) },

            // Capture rows inherit the surrounding load context, exactly like
            // list-literal elements and internal sequence joins: `X = (load('url'), 1)`
            // elaborates where `X = [load('url')]` does.
            Expr.Capture capture => capture with
            {
                Body = new OutputBundle(capture.Body.Select(row => ProcessExpr(row, context, depth + 1)).ToList()),
            },

            Expr.Binary binary => binary with
            {
                Left = ProcessExpr(binary.Left, LoadContext.RuntimeExpr, depth + 1),
                Right = ProcessExpr(binary.Right, LoadContext.RuntimeExpr, depth + 1),
            },

            // The link loop lives in its own helper so this calibrated frame keeps its size.
            Expr.Comparison comparison => ProcessComparison(comparison, depth),

            Expr.Unary unary => unary with { Operand = ProcessExpr(unary.Operand, LoadContext.RuntimeExpr, depth + 1) },

            Expr.Index index => index with
            {
                Target = ProcessExpr(index.Target, LoadContext.RuntimeExpr, depth + 1),
                Selector = ProcessExpr(index.Selector, LoadContext.RuntimeExpr, depth + 1),
            },

            // `with` keeps the stored spread-marker span intact alongside the node span.
            Expr.SequenceSpread spread => spread with { Operand = ProcessExpr(spread.Operand, context, depth + 1) },

            Expr.SequenceConstruct construct => construct with
            {
                Left = ProcessExpr(construct.Left, context, depth + 1),
                Right = ProcessExpr(construct.Right, context, depth + 1),
            },

            // List-literal elements inherit the surrounding load context,
            // exactly like capture rows (Expr.Capture) and internal sequence
            // joins: `X = [load('url')]` elaborates where
            // `X = (load('url'), 1)` does.
            Expr.ListLiteral list => list with
            {
                Items = list.Items.Select(item => ProcessExpr(item, context, depth + 1)).ToList(),
            },

            // `with` keeps every stored dot-edge fact (member span,
            // lexical fallback) intact — rebuilding positionally here
            // silently dropped the elaborated fallback identity for every
            // module-elaborated tree.
            Expr.DotCall dotCall => dotCall with
            {
                Target = ProcessExpr(dotCall.Target, dotCall.Args is null ? context : LoadContext.RuntimeExpr, depth + 1),
                Args = dotCall.Args is { } dotArgs
                    ? new OutputBundle(dotArgs.Select(argExpr => ProcessExpr(argExpr, LoadContext.RuntimeExpr, depth + 1)).ToList())
                    : null,
            },

            // `with` keeps the stored Grace weight intact — module
            // elaboration runs BEFORE parameter detection, so the
            // annotation is still live here.
            Expr.Grace grace => grace with { Inner = ProcessExpr(grace.Inner, context, depth + 1) },

            // Leaf nodes — no transformation needed
            Expr.Resolve or Expr.Param or Expr.Num or Expr.StringLiteral or Expr.BoolLiteral or Expr.EmptySequence or Expr.NativeCall => expr,
        };

        if (memo is not null)
            memo[expr] = result;
        return result;
    }

    /// <summary>
    /// MIRROR OF <see cref="ProcessExpr"/> — keep in lock-step. Runs only on
    /// load-bearing spines; every child routes through <see cref="RouteExprAsync"/> /
    /// <see cref="RouteAlgorithmAsync"/> so load-free children complete inline on the
    /// calibrated synchronous walk. The LINQ projections of the synchronous walk are
    /// explicit loops here because their element rewrites may await. The DAG-safety memo
    /// entry is stored from INSIDE this one state machine, only after the (possibly
    /// suspending) processing fully completed — a shared load CALL node is fetched,
    /// budget-charged, diagnosed, and spliced exactly once per (node, context, live depth), and no
    /// wrapper frame joins the recursion spine.
    /// </summary>
    private async ValueTask<Expr> ProcessExprAsync(Expr expr, LoadContext context, int depth)
    {
        ThrowIfInsufficientStack();

        // Childless leaves skip the memo, exactly as in the synchronous walk. Load-bearing
        // nodes key their rewrite by effective live depth as well as context (see the field
        // contract): depth can change a descendant load's pre-fetch admission verdict.
        Dictionary<int, Expr>? rewritesByDepth = null;
        var effectiveDepth = 0;
        if (AstTraversalDagSafety.HasTraversableExprChildren(expr))
        {
            var memo = _loadBearingExprWalkMemos[(int)context] ??=
                new(ReferenceEqualityComparer.Instance);
            if (!memo.TryGetValue(expr, out rewritesByDepth))
            {
                rewritesByDepth = [];
                memo[expr] = rewritesByDepth;
            }

            effectiveDepth = checked(_nestedTraversalBase + depth);
            if (rewritesByDepth.TryGetValue(effectiveDepth, out var memoized))
                return memoized;

            TraversalObservations?.RecordLoaderWalkExpansion();
        }

        Expr result;
        if (expr.TryGetUnresolvedLoadArguments(out var loadArgs))
        {
            result = await ProcessLoadAsync(loadArgs, context, expr.Span, depth).ConfigureAwait(false);
            if (rewritesByDepth is not null)
                rewritesByDepth[effectiveDepth] = result;
            return result;
        }

        switch (expr)
        {
            // Every rewrite is a `with` copy, exactly as in the synchronous walk (the record
            // copy carries the span and every other stored fact).
            case Expr.Call call:
            {
                var newFunc = await RouteExprAsync(call.Function, LoadContext.RuntimeExpr, depth + 1).ConfigureAwait(false);
                var newArgs = new List<Expr>(call.Args.Count);
                foreach (var argExpr in call.Args)
                    newArgs.Add(await RouteExprAsync(argExpr, LoadContext.RuntimeExpr, depth + 1).ConfigureAwait(false));
                result = call with { Function = newFunc, Args = new OutputBundle(newArgs) };
                break;
            }

            case Expr.AlgorithmExpr block:
                result = block with
                {
                    Algorithm = await RouteAlgorithmAsync(block.Algorithm, context, depth + 1).ConfigureAwait(false),
                };
                break;

            case Expr.Capture capture:
            {
                var newRows = new List<Expr>(capture.Body.Count);
                foreach (var row in capture.Body)
                    newRows.Add(await RouteExprAsync(row, context, depth + 1).ConfigureAwait(false));
                result = capture with { Body = new OutputBundle(newRows) };
                break;
            }

            case Expr.Binary binary:
                result = binary with
                {
                    Left = await RouteExprAsync(binary.Left, LoadContext.RuntimeExpr, depth + 1).ConfigureAwait(false),
                    Right = await RouteExprAsync(binary.Right, LoadContext.RuntimeExpr, depth + 1).ConfigureAwait(false),
                };
                break;

            case Expr.Comparison comparison:
                // The link loop lives in its own twin so this calibrated frame keeps its
                // size (the loop's list and cursor would otherwise be hoisted here).
                result = await RouteComparisonAsync(comparison, depth).ConfigureAwait(false);
                break;

            case Expr.Unary unary:
                result = unary with
                {
                    Operand = await RouteExprAsync(unary.Operand, LoadContext.RuntimeExpr, depth + 1).ConfigureAwait(false),
                };
                break;

            case Expr.Index index:
                result = index with
                {
                    Target = await RouteExprAsync(index.Target, LoadContext.RuntimeExpr, depth + 1).ConfigureAwait(false),
                    Selector = await RouteExprAsync(index.Selector, LoadContext.RuntimeExpr, depth + 1).ConfigureAwait(false),
                };
                break;

            case Expr.SequenceSpread spread:
                result = spread with
                {
                    Operand = await RouteExprAsync(spread.Operand, context, depth + 1).ConfigureAwait(false),
                };
                break;

            case Expr.SequenceConstruct construct:
                result = construct with
                {
                    Left = await RouteExprAsync(construct.Left, context, depth + 1).ConfigureAwait(false),
                    Right = await RouteExprAsync(construct.Right, context, depth + 1).ConfigureAwait(false),
                };
                break;

            case Expr.ListLiteral list:
            {
                var newItems = new List<Expr>(list.Items.Count);
                foreach (var item in list.Items)
                    newItems.Add(await RouteExprAsync(item, context, depth + 1).ConfigureAwait(false));
                result = list with { Items = newItems };
                break;
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
                result = dotCall with { Target = newTarget, Args = newArgs };
                break;
            }

            case Expr.Grace grace:
                result = grace with
                {
                    Inner = await RouteExprAsync(grace.Inner, context, depth + 1).ConfigureAwait(false),
                };
                break;

            // Leaf nodes — no transformation needed
            case Expr.Resolve:
            case Expr.Param:
            case Expr.Num:
            case Expr.StringLiteral:
            case Expr.BoolLiteral:
            case Expr.EmptySequence:
            case Expr.NativeCall:
                result = expr;
                break;

            // Runtime exhaustiveness guard. The synchronous twin is a compiler-exhaustive
            // switch expression; this twin stays a statement because its arms await inside
            // loops, and extracting them into helpers would add async state machines to the
            // calibrated recursion spine. A new Expr variant that the compiler forces into
            // the synchronous switch must be classified here by hand — the guard turns an
            // omission into a loud failure rather than a load silently left unelaborated.
            default:
                throw new InvalidOperationException(
                    $"Unhandled Expr variant in {nameof(ModuleLoader)}.{nameof(ProcessExprAsync)}: {expr.GetType().Name}. " +
                    "Classify the new variant explicitly as a recursive rewrite case or an intentional leaf, mirroring the synchronous walk.");
        }

        if (rewritesByDepth is not null)
            rewritesByDepth[effectiveDepth] = result;
        return result;
    }

    // ── load processing ────────────────────────────────────────────────────────────────

    /// <summary>
    /// Elaborates one load call. <paramref name="span"/> is the call's OWN span — the load
    /// site in the current document, or null for a load written inside a module (its import
    /// view carries no locations) or in a spanless host tree — and stays the span of the node
    /// spliced or substituted in its place, so a cached module view is never stamped with a
    /// caller position. Every diagnostic is positioned at the SITE: the call's own span when
    /// the document wrote it, otherwise the import site of the module content it lies in.
    /// </summary>
    private async ValueTask<Expr> ProcessLoadAsync(OutputBundle args, LoadContext context, SourceSpan? span, int depth)
    {
        var site = span ?? _importSite;

        // 1. Position check: load only allowed in property definitions and open lists
        if (context == LoadContext.RuntimeExpr)
        {
            ReportError(DiagnosticCode.InvalidLoadDirective, "load not allowed in runtime expression.", site);
            return new Expr.Num(0) { Span = span };
        }

        // 2. Extract URL: must be exactly 1 argument, must be a string literal
        var url = ExtractLoadUrl(args, site);
        if (url is null)
            return new Expr.Num(0) { Span = span };

        // 3. Target policy — the ONE admission point (ModuleLoadTarget): an HTTPS URL without
        // user information whose canonical host is allowed. From here on the target is its
        // canonical module URL — the identity the cycle check, the cache, the downloader, and
        // every diagnostic below share. Nothing above this line can invoke the downloader.
        var moduleUrl = AdmitLoadTarget(url, site);
        if (moduleUrl is null)
            return new Expr.Num(0) { Span = span };

        // 4. Cycle detection
        if (_inProgress.Contains(moduleUrl))
        {
            ReportError(DiagnosticCode.LoadCycle, $"load cycle detected: {moduleUrl}", site);
            return new Expr.Num(0) { Span = span };
        }

        // 5. Cache check — an already-elaborated module splices without re-traversal
        // or re-download, so it charges no cumulative traversal depth, no module slot, and
        // never suspends. The cached instance is ONE caller-independent import view: the
        // splice stamps only the wrapper node with this site's span. The front end still
        // elaborates the view once more in THIS site's scope (module content resolves against
        // the scope it is spliced into), so the splice charges the module's elaborated weight
        // against the aggregate: without it, K splices of one module in K distinct scopes cost
        // K times the module's elaboration — a product of two source sizes no per-source
        // ceiling bounds.
        if (_cache.TryGetValue(moduleUrl, out var cached))
        {
            if (!_budget.TryReserveAggregate(cached.Weight))
            {
                ReportSourceProcessingDiagnostic(SourceProcessingDiagnostics.AggregateSourceLengthExceededBySplice(
                    moduleUrl,
                    cached.Weight,
                    checked(_budget.AggregateSource + cached.Weight),
                    _budget.MaxAggregateSourceLength,
                    site));
                return new Expr.Num(0) { Span = span };
            }

            _spliceLedger.Charged += cached.Weight;
            return new Expr.AlgorithmExpr(cached.View) { Span = span };
        }

        // 6. Fetch + parse + splice — the loader's one awaiting path.
        return await FetchAndSpliceAsync(moduleUrl, span, site, depth).ConfigureAwait(false);
    }

    /// <summary>
    /// Extracts a URL string from load arguments.
    /// Must be exactly one argument that is a string literal.
    /// </summary>
    private string? ExtractLoadUrl(OutputBundle args, SourceSpan? site)
    {
        // load must have exactly 1 argument slot (the URL)
        if (args.Count != 1)
        {
            ReportError(DiagnosticCode.InvalidLoadDirective, "load requires exactly 1 argument (a URL string literal).", site);
            return null;
        }

        var urlExpr = args[0];

        // Must be a string literal
        if (urlExpr is Expr.StringLiteral(var url))
            return url;

        // Not a literal — could be Resolve("url"), a variable, or any other expression
        ReportError(DiagnosticCode.InvalidLoadDirective, "load URL must be a literal (non-dynamic).", site);
        return null;
    }

    /// <summary>
    /// Applies the load-target policy (<see cref="ModuleLoadTarget.TryAdmit"/>) to a written
    /// target: its canonical module URL, or null after reporting the refusal at
    /// <paramref name="site"/>. A synchronous leaf, so the verdict's temporaries never join
    /// <see cref="ProcessLoadAsync"/>'s state machine on the nested-load spine.
    /// </summary>
    private string? AdmitLoadTarget(string url, SourceSpan? site)
    {
        if (ModuleLoadTarget.TryAdmit(url, _allowedHosts, out var moduleUrl, out var rejection))
            return moduleUrl;

        ReportError(rejection.Code, rejection.Message, site);
        return null;
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
    /// <paramref name="span"/> is the load call's own span (the spliced node's span);
    /// <paramref name="site"/> is where every diagnostic is positioned (see
    /// <see cref="ProcessLoadAsync"/>) and the import site of everything inside the
    /// fetched module. <paramref name="moduleUrl"/> is the admitted target's canonical
    /// module URL (<see cref="ModuleLoadTarget"/>).
    ///
    /// <para><b>Accounting.</b> Every downloader INVOCATION consumes one module slot
    /// (<see cref="SourceProcessingLimits.MaxModuleCount"/>), committed immediately before the
    /// call and kept whatever the call returns: a failed, null, oversized, or
    /// aggregate-rejected download still happened, and re-fetching it for free at every load
    /// site let a source bound only by its own length drive an unbounded number of transport
    /// requests. Aggregate source is reserved only for text accepted for parsing. Host
    /// cancellation rolls back this frame's aggregate reservation, never its invocation. Every check
    /// that can refuse a load without its content — depth, module count, cumulative nesting,
    /// and cancellation — runs BEFORE the slot is committed and the downloader invoked.</para>
    /// </summary>
    private async ValueTask<Expr> FetchAndSpliceAsync(string moduleUrl, SourceSpan? span, SourceSpan? site, int depth)
    {
        // Import-depth ceiling: descend one level, or turn a would-be host stack overflow into a
        // structured diagnostic. Only reached on a cache MISS, so it bounds the true chain depth.
        // Paired with ExitModule in the finally below.
        if (!_budget.TryEnterModule())
        {
            ReportSourceProcessingDiagnostic(SourceProcessingDiagnostics.ModuleImportDepthExceeded(
                moduleUrl, _budget.CurrentDepth + 1, _budget.MaxModuleDepth, site));
            return new Expr.Num(0) { Span = span };
        }

        _inProgress.Add(moduleUrl);
        var hasAggregateReservation = false;
        var reservedSourceLength = 0;
        SpliceLedger? moduleLedger = null;
        try
        {
            // Module-count ceiling, checked BEFORE downloading (this is a cache miss), so a run
            // past the ceiling never pays for another download.
            if (!_budget.CanReserveModule())
            {
                ReportSourceProcessingDiagnostic(SourceProcessingDiagnostics.ModuleCountExceeded(
                    moduleUrl, _budget.ModuleCount + 1, _budget.MaxModuleCount, site));
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
                    moduleUrl, MaxTraversalDepth, site));
                return new Expr.Num(0) { Span = span };
            }

            // Fetch. The await is the elaboration's genuine suspension point: an
            // incomplete ValueTask unwinds to the host until the download completes,
            // then processing resumes here exactly once. `catch` around the await
            // uniformly covers a synchronously-throwing downloader and a faulted
            // awaitable.
            string source;
            ThrowIfCancellationRequested();

            // The download is about to happen: it consumes its module slot now and keeps it
            // whatever the downloader returns (see Accounting above). The capacity check above
            // guarantees the reservation; the loader is sequential, so nothing ran in between.
            if (!_budget.TryReserveModule())
                throw new InvalidOperationException("Internal error: the module-count reservation checked before the fetch was lost.");

            try
            {
                source = await _downloadCode(moduleUrl, _cancellationToken).ConfigureAwait(false);
                ThrowIfCancellationRequested();
            }
            catch (OperationCanceledException) when (IsCancellationRequested)
            {
                // Host cancellation is authoritative, including TOKEN IDENTITY. The
                // downloader may have faulted with its own timeout/cancellation token
                // while reacting to the request; normalize that race to the exact
                // configured source-processing token — or, for a deferred materialization
                // cancelled by the evaluation that requested it, to the active linked token
                // — instead of leaking the downloader's.
                ThrowIfCancellationRequested();
                throw; // Unreachable; keeps the compiler's flow analysis explicit.
            }
            catch (Exception ex)
            {
                // Cancellation is authoritative even if the downloader surfaced a different
                // exception while reacting to it. Only a still-active token permits a fetch
                // diagnostic (including downloader-owned cancellation/timeout exceptions).
                // The host's message can carry remote-controlled text (a status reason, a
                // response excerpt), so it is echoed bounded and with control characters escaped.
                ThrowIfCancellationRequested();
                ReportError(
                    DiagnosticCode.LoadFetchFailed,
                    $"load: failed to fetch '{moduleUrl}': {ModuleLoadTarget.EchoHostMessage(ex.Message)}",
                    site);
                return new Expr.Num(0) { Span = span };
            }

            if (source is null)
            {
                ReportError(DiagnosticCode.LoadFetchFailed, $"load: fetch for '{moduleUrl}' returned no source text.", site);
                return new Expr.Num(0) { Span = span };
            }

            // Per-module source-length ceiling, checked after download and before parsing, so an
            // oversized module never allocates tokens or nodes.
            if (!_budget.SourceLengthWithinLimit(source.Length))
            {
                ReportSourceProcessingDiagnostic(SourceProcessingDiagnostics.ModuleSourceLengthExceeded(
                    moduleUrl, source.Length, _budget.MaxSourceLength, site));
                return new Expr.Num(0) { Span = span };
            }

            // Aggregate-source ceiling: reserved only for text accepted for parsing; a rejected
            // reservation leaves the aggregate unchanged (the module slot stays consumed — the
            // download happened). An observed host cancellation rolls this active frame's
            // aggregate reservation back while unwinding, before the partial module can reach the cache.
            // Everything charged from here to the cache commit is this module's elaborated
            // weight: what a later splice of the cached view adds to the program.
            var aggregateBeforeModule = _budget.AggregateSource;
            var requestedTotal = checked(_budget.AggregateSource + source.Length);
            if (!_budget.TryReserveAggregate(source.Length))
            {
                ReportSourceProcessingDiagnostic(SourceProcessingDiagnostics.AggregateSourceLengthExceeded(
                    moduleUrl,
                    source.Length,
                    requestedTotal,
                    _budget.MaxAggregateSourceLength,
                    site));
                return new Expr.Num(0) { Span = span };
            }

            hasAggregateReservation = true;
            reservedSourceLength = source.Length;

            // Parse the fetched source as raw syntax, then elaborate nested loads
            // locally. This parse RUNS ABOVE the loader's live traversal frames, so
            // it starts with the conservative stack debt computed before the fetch:
            // the parser's cumulative recursion budget then bounds loader frames plus
            // parser frames TOGETHER (see NestedParseStackDebt for the combined
            // stack proof). A module whose nesting no longer fits the indebted
            // budget is rejected by the parser at the crossing token, and reported
            // here on the established load channel at the load site.
            ThrowIfCancellationRequested();
            // The module's own lexical and syntax diagnostics are summarized at the load site
            // below, never spliced into this document's list, so they go to a bag of their own —
            // of the run's capacity, so a malformed module never holds more than one list's
            // worth while it is classified (classification reads reported codes, not stored ones).
            var syntaxResult = Parser.ParseSyntax(source, parseStackDebt, _budget.CreateDiagnosticBag());

            if (syntaxResult.HasErrors)
            {
                if (HasStructuralBudgetDiagnostic(syntaxResult))
                {
                    ReportError(
                        DiagnosticCode.ModuleNestingTooDeep,
                        BuildLoadedSourceNestingErrorMessage(moduleUrl),
                        site);
                }
                else
                {
                    ReportError(
                        DiagnosticCode.InvalidLoadedSource,
                        BuildLoadedSourceParseErrorMessage(moduleUrl, source),
                        site);
                }

                return new Expr.Num(0) { Span = span };
            }

            // Propagate any non-error diagnostics (with context). The prefix is
            // presentation only; the structured code travels unchanged so the
            // nested diagnostic keeps its semantic family through the re-wrap. The
            // diagnostic's own span is positioned in the MODULE's text and never
            // leaves the loader: like every other module-parse outcome (a parse
            // error above is one InvalidLoadedSource at the load site) it is reported
            // at the site the current document wrote, so the parse result of this
            // document stays in this document's coordinate space.
            foreach (var diag in syntaxResult.Diagnostics)
            {
                _sink.Add(new Diagnostic(
                    $"[while loading {moduleUrl}] {diag.Message}",
                    diag.Severity,
                    site)
                {
                    Code = diag.Code,
                });
            }

            // The nested walk's errors decide whether the module may be cached, by COUNT: the
            // run's bag may already be full, and a full bag must not make a failing module cacheable.
            var nestedErrorsBefore = _sink.ReportedErrorCount;

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
                    moduleUrl, MaxTraversalDepth, site));
                return new Expr.Num(0) { Span = span };
            }

            // The source-coordinate boundary: the parsed module's own coordinates end here.
            // What crosses into this document's result is the module's locationless import
            // view (see ToImportView), taken once, before the nested loads inside it are
            // elaborated and before it can enter the cache, so every later splice shares
            // one caller-independent view.
            ThrowIfCancellationRequested();
            var importView = ToImportView(syntaxResult.SyntaxRoot);

            // Recursively elaborate any load calls in the fetched module. The fetched
            // tree gets its own load-bearing pre-scan so its load-free subtrees take
            // the synchronous walk too. Loads written inside the module have no span of
            // their own: their diagnostics are positioned at THIS load's site.
            MarkLoadBearing(importView);
            Algorithm elaborated;
            moduleLedger = new SpliceLedger();
            using (EnterNestedTraversal(traversalBase, site, moduleLedger))
            {
                elaborated = await RouteAlgorithmAsync(importView, LoadContext.TopLevel, depth: 1)
                    .ConfigureAwait(false);
            }

            // Cancellation never commits a partial module. This check also observes cancellation
            // requested during parsing or recursive elaboration before the cache write.
            ThrowIfCancellationRequested();

            // Mark the module root BEFORE caching so cache hits splice the same marked
            // instance: the mark is where the front end and the semantic model recognize
            // an import view (its own content carries no source locations).
            if (elaborated is Algorithm.User moduleRoot)
                elaborated = moduleRoot with { IsModuleElaborated = true };
            if (_sink.ReportedErrorCount == nestedErrorsBefore)
                _cache[moduleUrl] = new CachedModule(elaborated, checked((int)(_budget.AggregateSource - aggregateBeforeModule)));

            return new Expr.AlgorithmExpr(elaborated) { Span = span };
        }
        catch (OperationCanceledException) when (IsCancellationRequested)
        {
            // Abandoned source is not cached. Its aggregate reservations — its own source and
            // the splices its walk made — can be released, but the downloader invocation
            // already occurred and must stay charged: another evaluation of this parsed tree
            // can retry the cancelled deferred region. Nested modules that completed keep theirs.
            _budget.RollbackAggregate((hasAggregateReservation ? reservedSourceLength : 0) + (moduleLedger?.Charged ?? 0));

            throw;
        }
        finally
        {
            _inProgress.Remove(moduleUrl);
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

    // ── Error reporting ──────────────────────────────────────────────────────

    private static string BuildLoadedSourceParseErrorMessage(string moduleUrl, string source)
    {
        var sourceDescription = LooksLikeHtml(source)
            ? "the URL returned HTML instead of KatLang source"
            : "the downloaded content is not valid KatLang source";

        return $"load: cannot load '{moduleUrl}': {sourceDescription}. " +
            "Check that the URL is correct and points directly to a KatLang .kat file.";
    }

    /// <summary>
    /// True when a nested module's parse failed on the parser's cumulative recursion
    /// budget (which includes this loader's live-frame stack debt) or on the raw-syntax
    /// structural depth preflight, so the failure is a position-dependent nesting
    /// rejection rather than invalid module content. Classified by the diagnostics'
    /// structured <see cref="DiagnosticCode"/> families, never by message text; the
    /// per-chain <see cref="DiagnosticCode.ExpressionChainTooDeep"/> budget carries no
    /// loader stack debt and deliberately stays invalid-content, exactly as before. Read from
    /// the codes the parse REPORTED — a module with more lexical errors than one list keeps
    /// reports its nesting failure after its bag is full, and the classification must not
    /// change with the diagnostic budget.
    /// </summary>
    private static bool HasStructuralBudgetDiagnostic(SyntaxParseResult syntaxResult)
        => syntaxResult.Diagnostics.HasReported(DiagnosticCode.NestingTooDeep)
            || syntaxResult.Diagnostics.HasReported(DiagnosticCode.AstDepthLimitExceeded);

    private static string BuildLoadedSourceNestingErrorMessage(string moduleUrl)
        => $"load: loading '{moduleUrl}' at this position would nest module source too deeply to parse safely "
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

    private void ReportError(DiagnosticCode code, string message, SourceSpan? span)
        => _sink.Report(code, message, span);

    private void ReportSourceProcessingDiagnostic(Diagnostic diagnostic)
        => _sink.Add(diagnostic);
}
