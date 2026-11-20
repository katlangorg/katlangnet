using System.Runtime.ExceptionServices;
using System.Runtime.CompilerServices;

namespace KatLang.Evaluation;

/// <summary>
/// One node of a run's wait-for graph (NEED-09): a computation an observer can wait on. A
/// <see cref="NeedCell"/> is its own VALUE computation; a cell's RUNTIME CALLABLE projection is
/// a lazily held projection node of that cell. Both channels share these edges, the run's
/// gate, the one reachability test and the one cleanup rule, so VALUE→VALUE, VALUE→CALLABLE,
/// CALLABLE→VALUE and CALLABLE→CALLABLE waits form ONE graph with ONE cycle detector.
/// </summary>
internal abstract class NeedNode
{
    // The graph gate of suspended cells that belong to no run: only a test builds one (see
    // AddDependency). A Ready cell has no budget either, but it never takes part in an edge.
    private static readonly Lock UnownedDependencyGate = new();
    // The node whose computation the current logical flow is running: the parent of a VALUE
    // demand or of a runtime CALLABLE projection. Written only by EnterComputation and
    // LeaveComputation.
    private protected static readonly AsyncLocal<NeedNode?> Current = new();
    // The run this node belongs to (budget identity is graph identity).
    private protected readonly EvaluationBudget? _budget;
    // This node's active wait-for edges, each with its multiplicity (one per active observation
    // frame), in ONE of two forms (C# implementation only, 2026-11-19). Inline: at most one distinct
    // target, `_edge` with `_edgeCount` registrations, and no table. A synchronous run never has
    // more, because a computation demands its children one at a time. Promoted: a second distinct
    // target, which only overlapping asynchronous flows produce, moves every edge into
    // `_dependencies`, and the node keeps that table from then on (`_edge` stays null).
    private NeedNode? _edge;
    private int _edgeCount;
    private Dictionary<NeedNode, int>? _dependencies;

    private protected NeedNode(EvaluationBudget? budget) => _budget = budget;

    /// <summary>
    /// The comparer of every table keyed by nodes (C# implementation only, 2026-11-19): reference
    /// equality, hashed by <see cref="IdentityHash"/>. A cell's monitor is its gate
    /// (<see cref="NeedCell"/>), and on .NET locking an object whose header already holds its
    /// identity hash allocates an inflated monitor, so these tables never write a cell's header.
    /// </summary>
    internal sealed class IdentityComparer : IEqualityComparer<NeedNode>
    {
        internal static readonly IdentityComparer Instance = new();

        public bool Equals(NeedNode? x, NeedNode? y) => ReferenceEquals(x, y);

        public int GetHashCode(NeedNode node) => node.IdentityHash();
    }

    // A hash that is stable for the node's lifetime. Equal nodes are the same node, so any stable
    // value is correct; distinct nodes should rarely share one. A projection node's own header is
    // never locked.
    private protected virtual int IdentityHash() => RuntimeHelpers.GetHashCode(this);

    // The gate of this node's wait-for graph: its run's.
    private Lock DependencyGate => _budget?.NeedDependencyGate ?? UnownedDependencyGate;

    // Test observation only: how many distinct nodes this node's computation currently waits on
    // (its active wait-for edges). Every edge is gone once its observation frame exits.
    internal int ActiveDependencyCount
    {
        get { lock (DependencyGate) return _dependencies?.Count ?? (_edge is null ? 0 : 1); }
    }

    // Test observation only: whether this node's edges have been promoted to a table.
    internal bool HasPromotedDependencies
    {
        get { lock (DependencyGate) return _dependencies is not null; }
    }

    // Test observation only: whether the current logical flow is running some node's computation.
    internal static bool HasCurrentNode => Current.Value is not null;

    // Installs `node` as the flow's current node for a computation this flow starts, in both
    // families. The node is written to the logical context because a fork captured inside the
    // computation must inherit it. Returns the context captured before the write, and in `inner`
    // the context the write produced (each null while flow is suppressed), for LeaveComputation.
    private protected static ExecutionContext? EnterComputation(NeedNode node, out ExecutionContext? inner)
    {
        var outer = ExecutionContext.Capture();
        Current.Value = node;
        inner = ExecutionContext.Capture();
        return outer;
    }

    // Makes `parent` the flow's current node again once the computation has ended (C# implementation
    // only, 2026-11-20). If the flow's context is still `inner`, nothing has changed it since the node
    // was installed. Then `outer` holds exactly the values to restore, `parent` included, and restoring
    // that object allocates no new context. This saves one context per nested computation. Otherwise
    // only the node is written back, so a change made meanwhile is kept, such as a host's own AsyncLocal
    // or suppressed flow. A nested computation that left by this path restores its caller's `inner`
    // object, so the caller can take this path too.
    private protected static void LeaveComputation(NeedNode? parent, ExecutionContext? outer, ExecutionContext? inner)
    {
        if (outer is not null && inner is not null && ReferenceEquals(ExecutionContext.Capture(), inner))
            ExecutionContext.Restore(outer);
        else
            Current.Value = parent;
    }

    // All active edges, including independently started async chains, are checked
    // atomically before waiting. Iteration bounds the host stack independently of depth.
    // The graph is PER RUN: an edge joins two nodes of one budget, under that run's gate, and
    // a parent of another run records nothing. That parent is the AsyncLocal current node
    // flowing into a run a host operation starts inside the outer evaluation; no node of the
    // inner run can wait on it, so the skipped edge closes no cycle.
    internal bool AddDependency(NeedNode? parent)
    {
        if (parent is null || parent._budget != _budget) return true;
        lock (DependencyGate)
        {
            if (ReferenceEquals(this, parent) || ReachesLocked(parent)) return false;
            if (parent._dependencies is { } edges)
                edges[this] = edges.GetValueOrDefault(this) + 1;
            else if (parent._edge is null)
            {
                parent._edge = this;
                parent._edgeCount = 1;
            }
            else if (ReferenceEquals(parent._edge, this))
                parent._edgeCount++;
            else
            {
                // A second distinct target: promote both edges, multiplicities included.
                parent._dependencies = new(IdentityComparer.Instance)
                {
                    [parent._edge] = parent._edgeCount,
                    [this] = 1,
                };
                parent._edge = null;
                parent._edgeCount = 0;
            }
            return true;
        }
    }

    internal void RemoveDependency(NeedNode? parent)
    {
        if (parent is null || parent._budget != _budget) return;
        lock (DependencyGate)
        {
            if (parent._dependencies is { } edges)
            {
                var count = edges[this];
                if (count == 1) edges.Remove(this);
                else edges[this] = count - 1;
            }
            else
            {
                // Every removal pairs with its frame's successful AddDependency.
                if (!ReferenceEquals(parent._edge, this))
                    throw new System.Diagnostics.UnreachableException("NEED-09: a wait-for edge was removed that is not active.");
                if (--parent._edgeCount == 0) parent._edge = null;
            }
        }
    }

    // Whether the current logical flow is running INSIDE this node's computation: the flow's
    // current node is this node, or a node this node's computation is (transitively) waiting on.
    private protected bool IsActiveInCurrentFlow()
    {
        var current = Current.Value;
        if (current is null) return false;
        if (ReferenceEquals(current, this)) return true;
        if (current._budget != _budget) return false;
        lock (DependencyGate) return ReachesLocked(current);
    }

    // Whether `target` is reachable from this node through active edges. The caller holds the gate.
    private bool ReachesLocked(NeedNode target)
    {
        if (_edge is null && _dependencies is not { Count: > 0 }) return false;
        // Inline edges form a chain, walked without allocation. It ends: the graph is acyclic,
        // because AddDependency never adds an edge that closes a cycle.
        NeedNode node = this;
        while (node._dependencies is null)
        {
            if (ReferenceEquals(node, target)) return true;
            if (node._edge is not { } successor) return false;
            node = successor;
        }
        // From the first promoted node on, the general search.
        var pending = new Stack<NeedNode>();
        var visited = new HashSet<NeedNode>(IdentityComparer.Instance);
        pending.Push(node);
        while (pending.TryPop(out var next))
        {
            if (ReferenceEquals(next, target)) return true;
            if (!visited.Add(next)) continue;
            if (next._edge is { } edge) pending.Push(edge);
            if (next._dependencies is { } edges)
                foreach (var dependency in edges.Keys) pending.Push(dependency);
        }
        return false;
    }
}

/// <summary>
/// One invocation's supplied computation. VALUE completion and CALLABLE identity are
/// independent; transport shares this object. No demand bookkeeping is a language step.
/// <para><b>Concurrency contract.</b></para>
/// <list type="bullet">
///   <item><b>Run-scoped.</b> A cell belongs to the ONE run whose budget it carries. Supported run
///   entry points export only values through results and host callbacks. Internal cache keys can retain
///   cells through execution environments, but cache entries include run identity and expose only
///   values. Internal test adapters must not replay retained evaluation delegates in another run.
///   The evaluator demands a run's cells
///   from one logical flow at a time, and an async continuation may resume that flow on another
///   thread.</item>
///   <item><b>Thread-safe anyway.</b> Overlapping demands of one cell join a single flight (NEED-09).
///   The flight starts at most once; success, ordinary failure, host exception and cancellation
///   are sticky; and the completed outcome is never rewritten. A VALUE flight's shared completion
///   is created by its first joiner: a computation nobody joins allocates none.</item>
///   <item><b>The per-cell gate</b> is the cell's own monitor (<c>lock (this)</c>; C# implementation
///   only since 2026-11-19, formerly a separate gate object per cell). It guards the cell's own state,
///   both channels. It is held only for field updates and for an IDENTITY-ONLY CALLABLE projection,
///   which evaluates nothing and demands no VALUE. No other code locks a cell: the type is internal,
///   and nothing else in KatLang takes a cell's monitor.</item>
///   <item><b>The wait-for graph</b> (<see cref="NeedNode"/>, NEED-09) belongs to the run: its
///   gate is the run budget's <see cref="EvaluationBudget.NeedDependencyGate"/>. A cycle is detected
///   before its closing edge is awaited, across overlapping async chains too. Independent runs
///   never contend for one gate. The graph lock is never held while user code runs or a flight is
///   awaited, and the two gates are never nested.</item>
///   <item><b>Cleanup.</b> An edge exists exactly while its observation frame is active. It is removed
///   on every exit: success, failure, exception, cancellation or a cycle.</item>
///   <item><b>Cells without a budget.</b> A Ready cell carries no budget but never joins a graph: it
///   is complete before any edge is considered, and it is never a demand's parent. A suspended cell
///   without a budget, which only a test builds, shares one process-wide fallback graph.</item>
/// </list>
/// <para><b>CALLABLE channel (META-S3-0a; Lean <c>NeedCallableState</c>, <c>NeedProjection.step</c>).</b>
/// Every projection other than a runtime one is IDENTITY-ONLY: it is computed under the
/// cell gate and memoized, with no node, flight or edge — it cannot be re-entered, so Lean's
/// <c>projecting</c> marker is unobservable for it (<c>transparent_projection_is_marker_free</c>).
/// A RUNTIME projection — one whose computation may demand VALUE or project other cells — is
/// the cell's <see cref="ProjectionNode"/> in the run's graph and follows the VALUE protocol
/// exactly: one computation outside the gate, independent observers join its completion,
/// re-entry in the same logical flow is <see cref="EvalError.DemandCycle"/> for the re-entering
/// observation only, and the computation's outcome is sticky. Since META-S3-1 a source program reaches
/// one through a supplied <c>X.Algorithm</c> link or a parameter-rooted dot path in a run that has
/// runtime projections (<see cref="Evaluator.SupplyCell"/>); <see cref="WithRuntimeProjection"/> is the
/// host-built construction point.</para>
/// </summary>
internal sealed class NeedCell : NeedNode
{
    private readonly CancellationToken _token;
    private readonly bool _ready;
    private Func<EvalResult<Evaluator.CountedResult>>? _evaluate;
    private Func<ValueTask<EvalResult<Evaluator.CountedResult>>>? _evaluateAsync;
    // A host-built cell's CALLABLE computation: an identity-only projection delegate, or the
    // RUNTIME projection's node (which holds its flight state). A written argument's cell has
    // neither: its identity-only projection is the evaluator's operation over its suspension.
    private readonly object? _projection;
    // The VALUE flight: null before the computation starts and after it ends; UnjoinedFlight
    // while it runs with no other observer; a shared completion once a second observer joins.
    private TaskCompletionSource<EvalResult<Evaluator.CountedResult>>? _flight;
    // The flight of a running VALUE computation no other observer has joined (never completed,
    // never awaited): its starter returns the outcome it published itself, so the completion a
    // joiner awaits is allocated by the first joiner, under the gate (NEED-09 single flight).
    private static readonly TaskCompletionSource<EvalResult<Evaluator.CountedResult>> UnjoinedFlight = new();
    private EvalResult<Evaluator.CountedResult>? _completed;
    private ExceptionDispatchInfo? _exception;
    private EvalResult<Algorithm?>? _callable;
    // A written argument's suspension (Lean `NeedSuspension.expression source caller values`),
    // kept as DATA rather than as closures over it. It is never cleared: CALLABLE projection may
    // run after VALUE completion, and an invocation plan executes over it again (S0).
    private readonly Evaluator.ExpressionSuspension? _suspension;

    /// <summary>
    /// The wait-for node of a cell's RUNTIME CALLABLE projection: the CALLABLE twin of the cell's
    /// own VALUE node. It carries the projection's computation and its flight and the stored host
    /// exception or cancellation; the outcome itself is the cell's CALLABLE memo. As for VALUE, the
    /// flight's shared completion is created by its first joiner (C# implementation only,
    /// 2026-11-19): a computation nobody joins allocates none. Every field is guarded by
    /// the owning cell's gate. The computation and the completion are released once it ends. A
    /// written argument's node carries no delegates: its computation is the evaluator's projection
    /// of the cell's own suspension (<see cref="Evaluator.ProjectSuspendedCallable"/>).
    /// </summary>
    private sealed class ProjectionNode(
        EvaluationBudget? budget,
        Func<EvalResult<Algorithm?>>? project,
        Func<ValueTask<EvalResult<Algorithm?>>>? projectAsync) : NeedNode(budget)
    {
        // The flight of a running projection no other observer has joined (never completed, never
        // awaited): its starter returns the outcome it published itself.
        internal static readonly TaskCompletionSource<EvalResult<Algorithm?>> UnjoinedFlight = new();

        internal Func<EvalResult<Algorithm?>>? Project = project;
        internal Func<ValueTask<EvalResult<Algorithm?>>>? ProjectAsync = projectAsync;
        // Null before the computation starts and after it ends; UnjoinedFlight while it runs with
        // no other observer; a shared completion once a second observer joins.
        internal TaskCompletionSource<EvalResult<Algorithm?>>? Flight;
        internal ExceptionDispatchInfo? Exception;
        // Test observation only: how many computations started (at most one).
        internal int Computations;
    }

    internal NeedCell(
        Func<EvalResult<Evaluator.CountedResult>> evaluate,
        Func<ValueTask<EvalResult<Evaluator.CountedResult>>> evaluateAsync,
        Func<EvalResult<Algorithm?>>? project = null,
        SourceSpan? span = null,
        IReadOnlyList<NeedCell>? slice = null,
        Expr? source = null,
        EvaluationBudget? budget = null,
        CancellationToken token = default)
        : this(evaluate, evaluateAsync, (object?)project, span, slice, source, budget, token)
    {
    }

    private NeedCell(
        Func<EvalResult<Evaluator.CountedResult>> evaluate,
        Func<ValueTask<EvalResult<Evaluator.CountedResult>>> evaluateAsync,
        object? projection,
        SourceSpan? span,
        IReadOnlyList<NeedCell>? slice,
        Expr? source,
        EvaluationBudget? budget,
        CancellationToken token)
        : base(budget)
    {
        _evaluate = evaluate;
        _evaluateAsync = evaluateAsync;
        _projection = projection;
        _token = token;
        Span = span;
        Slice = slice;
        Source = source;
    }

    // ── META-S3-0b: non-initiating observation ───────────────────────────────────────────────
    // An observation is SYNCHRONOUS — it never awaits, blocks or starts a computation — so the
    // scope of the flow running it is exactly the thread's innermost scope.
    [ThreadStatic] private static ObservationScope? t_observation;

    /// <summary>The channel of a pending operation: a cell's VALUE or its runtime CALLABLE projection.</summary>
    internal enum Channel { Value, Callable }

    /// <summary>
    /// The outcomes ONE asynchronous resolution has awaited (<c>Evaluator.ResolveAsync</c>),
    /// published or not — a re-entry's flow-local <see cref="EvalError.DemandCycle"/> included —
    /// keyed by (cell, channel) and replayed at the demand point where the resolver reads them.
    /// It belongs to that resolution alone: a nested observation scope never sees it.
    /// <para>The first recorded pair is held inline, and later pairs go to a table for their
    /// channel (C# implementation only, 2026-11-20). Almost every resolution that performs a step
    /// performs exactly one, so it allocates no table.</para>
    /// </summary>
    internal sealed class ResolutionRecord
    {
        private NeedCell? _firstCell;
        private Channel _firstChannel;
        private EvalResult<Evaluator.CountedResult> _firstValue;
        private EvalResult<Algorithm?> _firstCallable;
        private Dictionary<NeedCell, EvalResult<Evaluator.CountedResult>>? _values;
        private Dictionary<NeedCell, EvalResult<Algorithm?>>? _callables;

        internal bool Contains(NeedCell cell, Channel channel)
            => IsFirst(cell, channel)
                || (channel == Channel.Value ? _values?.ContainsKey(cell) == true : _callables?.ContainsKey(cell) == true);

        internal void RecordValue(NeedCell cell, EvalResult<Evaluator.CountedResult> outcome)
        {
            if (TakeFirst(cell, Channel.Value)) _firstValue = outcome;
            else (_values ??= new(IdentityComparer.Instance)).Add(cell, outcome);
        }

        internal void RecordCallable(NeedCell cell, EvalResult<Algorithm?> outcome)
        {
            if (TakeFirst(cell, Channel.Callable)) _firstCallable = outcome;
            else (_callables ??= new(IdentityComparer.Instance)).Add(cell, outcome);
        }

        internal bool TryGetValue(NeedCell cell, out EvalResult<Evaluator.CountedResult> outcome)
        {
            if (IsFirst(cell, Channel.Value))
            {
                outcome = _firstValue;
                return true;
            }
            if (_values is not null && _values.TryGetValue(cell, out outcome)) return true;
            outcome = default;
            return false;
        }

        internal bool TryGetCallable(NeedCell cell, out EvalResult<Algorithm?> outcome)
        {
            if (IsFirst(cell, Channel.Callable))
            {
                outcome = _firstCallable;
                return true;
            }
            if (_callables is not null && _callables.TryGetValue(cell, out outcome)) return true;
            outcome = default;
            return false;
        }

        private bool IsFirst(NeedCell cell, Channel channel) => ReferenceEquals(_firstCell, cell) && _firstChannel == channel;

        // Claims the inline slot for the first pair recorded. A pair is recorded at most once, because
        // Guard A never performs a recorded pair again. A repeat throws, as the tables' Add does.
        private bool TakeFirst(NeedCell cell, Channel channel)
        {
            if (_firstCell is null)
            {
                _firstCell = cell;
                _firstChannel = channel;
                return true;
            }
            if (IsFirst(cell, channel))
                throw new ArgumentException("META-S3-0b: a resolution recorded the same operation twice.");
            return false;
        }

        /// <summary>
        /// An untainted alias chase this resolution's previous attempt suspended at the runtime projection it reported
        /// pending (<c>Evaluator.AliasChaseMachine</c>, C# implementation-only): the retry resumes it there
        /// instead of re-walking the chain above that projection. Flow-local, like every outcome here.
        /// </summary>
        internal object? ParkedChase { get; set; }
    }

    /// <summary>
    /// A NON-INITIATING observation scope: inside it the synchronous resolver runs normally over
    /// completed and identity-only facts, but a VALUE that is not complete and a runtime CALLABLE
    /// projection that is not published are never started. Such an observation answers, in this
    /// order: cancellation and run terminality (the cell's ordinary entry checks), the completed
    /// memo or stored exception, the outcome the scope's resolution recorded for that pair, and
    /// otherwise <see cref="EvalError.ObservationPending"/> — recording the FIRST such pair as the
    /// scope's <see cref="Pending"/> operation. Nothing computed while a pair is pending is
    /// memoized. Every scope is exited by its owner on every path (<see cref="ExitObservation"/>).
    /// </summary>
    internal sealed class ObservationScope
    {
        internal ObservationScope(ObservationScope? outer, ResolutionRecord? record)
        {
            Outer = outer;
            Record = record;
        }

        internal ObservationScope? Outer { get; }
        internal ResolutionRecord? Record { get; }
        internal NeedCell? Pending { get; private set; }
        internal Channel PendingChannel { get; private set; }

        internal EvalResult<Evaluator.CountedResult> ObserveValue(NeedCell cell)
        {
            if (Record is not null && Record.TryGetValue(cell, out var recorded)) return recorded;
            return MarkPending(cell, Channel.Value);
        }

        internal EvalResult<Algorithm?> ObserveCallable(NeedCell cell)
        {
            if (Record is not null && Record.TryGetCallable(cell, out var recorded)) return recorded;
            return MarkPending(cell, Channel.Callable);
        }

        // The ONE primitive that reports a pair pending (keeps the FIRST). Every cell observation
        // consults the record first; Evaluator.ResolveAsync's Guard A fails loud should any route
        // ever report a recorded pair pending again.
        internal EvalError MarkPending(NeedCell cell, Channel channel)
        {
            if (Pending is null)
            {
                Pending = cell;
                PendingChannel = channel;
            }
            return EvalError.ObservationPending.Instance;
        }
    }

    /// <summary>Whether <paramref name="error"/> is (or wraps) a non-initiating observation's pending marker.</summary>
    internal static bool IsObservationPending(EvalError error)
    {
        while (error is EvalError.WithContext withContext) error = withContext.Inner;
        return error is EvalError.ObservationPending;
    }

    /// <summary>Whether the current flow is inside a non-initiating observation scope.</summary>
    internal static bool IsObserving => t_observation is not null;

    /// <summary>The current flow's innermost observation scope, if any.</summary>
    internal static ObservationScope? CurrentObservation => t_observation;

    internal static ObservationScope EnterObservation(ResolutionRecord? record = null)
        => t_observation = new ObservationScope(t_observation, record);

    internal static void ExitObservation(ObservationScope scope)
    {
        if (!ReferenceEquals(t_observation, scope))
            throw new System.Diagnostics.UnreachableException("META-S3-0b: observation scopes exited out of order.");
        t_observation = scope.Outer;
    }

    /// <summary>
    /// Guard B (META-S3-0b progress invariant): a resolution reaches only RETRY-STABLE cells —
    /// cells that exist independently of it, or are retained by an owner that does. A runtime
    /// projection cell allocated FRESH while a non-initiating observation runs would be new at
    /// every retry (never memoized, never replayed), so its allocation boundary is wrong. Every
    /// fresh runtime-projection allocation calls this; a CAS-established cell retained by a
    /// stable owner is not a fresh allocation.
    /// </summary>
    internal static void ThrowIfAllocatingRuntimeProjectionWhileObserving()
    {
        if (t_observation is not null)
            throw new System.Diagnostics.UnreachableException(
                "META-S3-0b: a runtime-projection cell was allocated inside a non-initiating observation (not retry-stable).");
    }

    /// <summary>
    /// A written argument's cell (<see cref="Evaluator.SupplyCell"/>): its VALUE, async VALUE and
    /// CALLABLE projection are the evaluator's static operations over <paramref name="suspension"/>,
    /// so the cell allocates no delegate or closure of its own. A cell whose CALLABLE is a RUNTIME
    /// projection (<paramref name="runtimeProjection"/>, META-S3-1: a supplied <c>X.Algorithm</c> link or
    /// a parameter-rooted dot path, <see cref="Evaluator.SupplyCell"/>) also gets its projection node,
    /// whose computation projects that same suspension, and marks its run as one with runtime
    /// projections; the caller decides whether the allocation is fresh (Guard B).
    /// </summary>
    internal NeedCell(Expr source, Evaluator.ExpressionSuspension suspension, EvaluationBudget budget,
        bool runtimeProjection, CancellationToken token)
        : base(budget)
    {
        _suspension = suspension;
        _token = token;
        if (runtimeProjection)
        {
            budget.NoteRuntimeProjection();
            _projection = new ProjectionNode(budget, null, null);
        }
        Span = source.Span;
        Source = source;
        // An invocation plan's identity IS its one owning cell (Lean: the need address).
        if (suspension is Evaluator.InvocationPlan plan) plan.Attach(this);
    }

    /// <summary>
    /// A host-built cell whose CALLABLE channel is a RUNTIME projection: <paramref name="project"/>
    /// / <paramref name="projectAsync"/> may demand other cells' VALUE and project other cells'
    /// CALLABLE, so the projection runs as this cell's <see cref="ProjectionNode"/> in the run's
    /// wait-for graph under the CALLABLE single flight. This is the internal construction point
    /// of the runtime projection machinery; a written argument's cell gets its node from its own
    /// constructor (META-S3-1).
    /// </summary>
    internal static NeedCell WithRuntimeProjection(
        Func<EvalResult<Evaluator.CountedResult>> evaluate,
        Func<ValueTask<EvalResult<Evaluator.CountedResult>>> evaluateAsync,
        Func<EvalResult<Algorithm?>> project,
        Func<ValueTask<EvalResult<Algorithm?>>> projectAsync,
        SourceSpan? span = null,
        EvaluationBudget? budget = null,
        CancellationToken token = default)
    {
        ThrowIfAllocatingRuntimeProjectionWhileObserving();
        // The run now has a runtime projection: its resolutions observe before they initiate.
        budget?.NoteRuntimeProjection();
        return new(evaluate, evaluateAsync, new ProjectionNode(budget, project, projectAsync), span, null, null, budget, token);
    }

    /// <summary>
    /// The written argument's suspension, or <c>null</c> for a Ready, collector or host-built cell.
    /// An <see cref="Evaluator.InvocationPlan"/> suspension marks the cell as an invocation plan (S0).
    /// </summary>
    internal Evaluator.ExpressionSuspension? Suspension => _suspension;

    // The identity hash of a readonly object that belongs to this cell and that nobody locks: the
    // written argument's suspension, the host-built cell's projection, or the collector's slice.
    // It leaves this cell's header to its monitor. A Ready cell has none of them, but it is complete,
    // so no edge or resolution record ever keys on it. Only a test-built cell without a projection
    // falls back to its own header, which costs time, never correctness.
    private protected override int IdentityHash()
        => RuntimeHelpers.GetHashCode(_suspension ?? _projection ?? (object?)Slice ?? this);

    // Test observation only: whether this cell's VALUE has completed (successfully or not).
    internal bool HasCompletedValue
    {
        get { lock (this) return _completed is not null || _exception is not null; }
    }

    // Test observation only: whether this cell's VALUE computation is in flight (its completion
    // is released once the outcome is published).
    internal bool HasValueInFlight
    {
        get { lock (this) return _flight is not null; }
    }

    // Test observation only: whether a second observer has joined the running VALUE computation,
    // so its shared completion exists.
    internal bool HasJoinedValueFlight
    {
        get { lock (this) return _flight is not null && !ReferenceEquals(_flight, UnjoinedFlight); }
    }

    // Test observation only: whether this cell's CALLABLE outcome is memoized.
    internal bool HasCallableMemo
    {
        get { lock (this) return _callable is not null; }
    }

    /// <summary>
    /// Whether <paramref name="outcome"/>, just returned by <see cref="ProjectCallable"/>, IS this cell's PUBLISHED
    /// CALLABLE outcome — the sticky outcome every later observer reads first, success or failure — rather than
    /// an unpublished outcome (a resolution's recorded-only result, a flow-local <see cref="EvalError.DemandCycle"/>,
    /// a pending observation or terminal answer). An alias chase settles a route decision only when every
    /// projection it read was published (<c>Evaluator.AliasChaseMachine</c>).
    /// </summary>
    internal bool IsPublishedCallable(EvalResult<Algorithm?> outcome)
    {
        lock (this)
        {
            return _callable is { } published
                && (published.IsError
                    ? outcome.IsError && ReferenceEquals(published.Error, outcome.Error)
                    : outcome.IsOk && ReferenceEquals(published.Value, outcome.Value));
        }
    }

    // Test observation only: whether this cell's CALLABLE is a runtime projection, how many of
    // its computations started, whether one is in flight, whether a second observer has joined it
    // (so its shared completion exists), and its node's active wait-for edges.
    internal bool HasRuntimeProjection => _projection is ProjectionNode;

    internal int ProjectionComputations
    {
        get { lock (this) return (_projection as ProjectionNode)?.Computations ?? 0; }
    }

    internal bool HasProjectionInFlight
    {
        get { lock (this) return (_projection as ProjectionNode)?.Flight is not null; }
    }

    internal bool HasJoinedProjectionFlight
    {
        get
        {
            lock (this)
                return (_projection as ProjectionNode)?.Flight is { } flight && !ReferenceEquals(flight, ProjectionNode.UnjoinedFlight);
        }
    }

    internal int ProjectionActiveDependencyCount => (_projection as ProjectionNode)?.ActiveDependencyCount ?? 0;

    // Produced data is a calculation value: it never carries callable identity.
    private NeedCell(Evaluator.CountedResult value)
        : base(null)
    {
        _ready = true;
        _completed = EvalResult<Evaluator.CountedResult>.Ok(value);
        _callable = EvalResult<Algorithm?>.Ok(null);
    }

    internal SourceSpan? Span { get; }
    internal Expr? Source { get; }
    internal IReadOnlyList<NeedCell>? Slice { get; }

    internal static NeedCell Ready(Evaluator.CountedResult value) => new(value);

    // Planning may inspect an already-supplied data value. A suspended computation
    // is never run, nor treated as ready because another demand happened to complete it.
    internal bool TryGetReadyValue(out Evaluator.CountedResult value)
    {
        if (_ready)
        {
            value = _completed!.Value.Value;
            return true;
        }
        value = default;
        return false;
    }

    internal EvalResult<Algorithm?> ProjectCallable()
    {
        _token.ThrowIfCancellationRequested();
        var terminal = _budget?.CheckContinuation();
        if (_projection is ProjectionNode node) return ProjectRuntime(node, terminal);
        if (terminal is not null) return terminal;
        lock (this)
        {
            if (_exception?.SourceException is OperationCanceledException) _exception.Throw();
            if (_callable is { } known) return known;
            var computed = _suspension is not null
                ? Evaluator.ProjectSuspendedCallable(this, Source!, _suspension)
                : (_projection as Func<EvalResult<Algorithm?>>)?.Invoke() ?? EvalResult<Algorithm?>.Ok(null);
            // An identity-only projection can reach another cell's runtime projection (a
            // parameter-rooted path). Inside a non-initiating observation with a pending
            // operation, its result is not this cell's outcome (it may be the pending marker
            // itself), so it is not published; the retried observation computes it again.
            if (t_observation is { Pending: not null }) return computed;
            _callable = computed;
            return computed;
        }
    }

    /// <summary>
    /// Diagnostic enrichment's CALLABLE read (META-S3-0b, non-initiating): the identity when it is
    /// already known or identity-only to compute, <c>null</c> when there is none, the projection
    /// failed, or it would need a runtime step — which is never started for a message choice.
    /// </summary>
    internal Algorithm? PeekCallable()
    {
        // Budgetless runtime cells are supported by the internal construction seam too;
        // their missing run flag must never turn a diagnostic peek into a computation.
        if (_projection is not ProjectionNode && _budget is not { HasRuntimeProjections: true })
        {
            var direct = ProjectCallable();
            return direct.IsOk ? direct.Value : null;
        }
        var scope = EnterObservation();
        try
        {
            var observed = ProjectCallable();
            return scope.Pending is null && observed.IsOk ? observed.Value : null;
        }
        finally { ExitObservation(scope); }
    }

    /// <summary>
    /// The asynchronous CALLABLE observation: a runtime projection's computation is awaited
    /// (its flight is the one <see cref="ProjectCallable"/> joins); an identity-only projection
    /// evaluates nothing, so it is the synchronous projection.
    /// </summary>
    internal ValueTask<EvalResult<Algorithm?>> ProjectCallableAsync()
        => _projection is ProjectionNode node ? ProjectRuntimeAsync(node) : new(ProjectCallable());

    // Observation entry of a runtime projection, VALUE's order: a terminal run answers first
    // (a completed projection's own resource failure keeps its provenance), then a stored
    // cancellation or host exception, then the memo. `null` = no outcome yet.
    private EvalResult<Algorithm?>? ObserveProjected(ProjectionNode node, EvalError? terminal)
    {
        lock (this)
        {
            if (terminal is not null)
                return _callable is { IsError: true } failed && failed.Error.IsResourceLimit ? failed : terminal;
            if (_exception?.SourceException is OperationCanceledException) _exception.Throw();
            node.Exception?.Throw();
            return _callable;
        }
    }

    // The runtime projection's single flight: Demand's protocol on the projection node.
    private EvalResult<Algorithm?> ProjectRuntime(ProjectionNode node, EvalError? terminal)
    {
        if (ObserveProjected(node, terminal) is { } known) return known;
        // META-S3-0b: a non-initiating observation never starts (or joins) the computation; it
        // reads the outcome its resolution recorded, or reports this projection pending.
        if (t_observation is { } observation) return observation.ObserveCallable(this);
        // An asynchronous run resolves an unpublished runtime projection through the async
        // resolution adapter (Evaluator.ResolveAsync) or an awaiting consumer, never by blocking.
        if (_budget is { IsAsynchronousRun: true })
            throw new System.Diagnostics.UnreachableException(
                "META-S3-0b: an unpublished runtime CALLABLE projection was reached synchronously in an asynchronous run (missing async resolution site).");
        var parent = Current.Value;
        if (!node.AddDependency(parent))
            return new EvalError.DemandCycle { Span = Span };
        try
        {
            Task<EvalResult<Algorithm?>>? task;
            lock (this)
            {
                if (_callable is { } completed) return completed;
                node.Exception?.Throw();
                task = JoinOrStartProjectionFlight(node);
            }
            if (task is null)
            {
                var outer = EnterComputation(node, out var inner);
                try { CompleteProjection(node, RuntimeHelpers.TryEnsureSufficientExecutionStack()
                    ? _suspension is not null ? Evaluator.ProjectSuspendedCallable(this, Source!, _suspension) : node.Project!()
                    : new EvalError.EvaluationStackExhausted { Span = Span }); }
                catch (Exception error) { CompleteProjectionException(node, error); }
                finally { LeaveComputation(parent, outer, inner); }
                return ProjectionStarterOutcome(node);
            }
            try { return task.GetAwaiter().GetResult(); }
            catch
            {
                // As in Demand: preserve the original host exception and token.
                lock (this) node.Exception?.Throw();
                throw;
            }
        }
        finally { node.RemoveDependency(parent); }
    }

    private async ValueTask<EvalResult<Algorithm?>> ProjectRuntimeAsync(ProjectionNode node)
    {
        _token.ThrowIfCancellationRequested();
        if (ObserveProjected(node, _budget?.CheckContinuation()) is { } known) return known;
        ThrowIfInitiatingWhileObserving();
        var parent = Current.Value;
        if (!node.AddDependency(parent))
            return new EvalError.DemandCycle { Span = Span };
        try
        {
            Task<EvalResult<Algorithm?>>? task;
            lock (this)
            {
                if (_callable is { } completed) return completed;
                node.Exception?.Throw();
                task = JoinOrStartProjectionFlight(node);
            }
            if (task is null)
            {
                await ProjectRuntimeComputationAsync(node).ConfigureAwait(false);
                return ProjectionStarterOutcome(node);
            }
            try { return await task.ConfigureAwait(false); }
            catch
            {
                lock (this) node.Exception?.Throw();
                throw;
            }
        }
        finally { node.RemoveDependency(parent); }
    }

    private async ValueTask ProjectRuntimeComputationAsync(ProjectionNode node)
    {
        // TWIN-ONLY (intentional difference from the synchronous ProjectRuntime): see StackHop.
        if (StackHop.HostStackIsLow()) await new StackHop();
        var previous = Current.Value;
        var outer = EnterComputation(node, out var inner);
        try { CompleteProjection(node, RuntimeHelpers.TryEnsureSufficientExecutionStack()
            ? _suspension is not null
                ? await Evaluator.ProjectSuspendedCallableAsync(this, Source!, _suspension).ConfigureAwait(false)
                : await node.ProjectAsync!().ConfigureAwait(false)
            : new EvalError.EvaluationStackExhausted { Span = Span }); }
        catch (Exception error) { CompleteProjectionException(node, error); }
        finally { LeaveComputation(previous, outer, inner); }
    }

    // Under the gate, with no outcome yet: starts the runtime projection's flight (null: the caller
    // computes) or joins it, creating the shared completion when this is its first joiner.
    private static Task<EvalResult<Algorithm?>>? JoinOrStartProjectionFlight(ProjectionNode node)
    {
        if (node.Flight is null)
        {
            node.Flight = ProjectionNode.UnjoinedFlight;
            node.Computations++;
            return null;
        }
        if (ReferenceEquals(node.Flight, ProjectionNode.UnjoinedFlight))
            node.Flight = new(TaskCreationOptions.RunContinuationsAsynchronously);
        return node.Flight.Task;
    }

    // The projection starter's outcome once its computation has ended: exactly what awaiting the
    // shared completion delivers (the memo, or the stored exception rethrown, as a joiner's catch
    // does). The computation wrote it before this read and nothing rewrites it.
    private EvalResult<Algorithm?> ProjectionStarterOutcome(ProjectionNode node)
    {
        if (_callable is { } completed) return completed;
        node.Exception!.Throw();
        throw new System.Diagnostics.UnreachableException();
    }

    // A non-initiating observation is synchronous: an asynchronous start inside one means a
    // synchronous resolver blocked on asynchronous work, which would initiate it.
    private static void ThrowIfInitiatingWhileObserving()
    {
        if (t_observation is not null)
            throw new System.Diagnostics.UnreachableException(
                "META-S3-0b: an asynchronous demand or projection was started inside a non-initiating observation.");
    }

    private void CompleteProjection(ProjectionNode node, EvalResult<Algorithm?> result)
    {
        if (result.IsError && IsObservationPending(result.Error))
            throw EvalError.ObservationPending.Escaped();
        if (result.IsError && result.Error.IsResourceLimit) _budget?.RetainTerminal(result.Error);
        // META-S3-0b provenance (NEED-06): an ordinary failure of a RUNTIME projection is a
        // failed computation, never "no identity" — marked once, here, for the absence
        // classifiers. A resource limit stays the run's retained object (terminal anyway).
        else if (result.IsError && !result.Error.IsProjectionFailure)
            result = result.Error with { IsProjectionFailure = true };
        lock (this)
        {
            // Published with the completion: every later observer reads the memo first, so the
            // released completion and computation are never needed again.
            _callable = result;
            var flight = node.Flight!;
            node.Flight = null;
            node.Project = null;
            node.ProjectAsync = null;
            if (!ReferenceEquals(flight, ProjectionNode.UnjoinedFlight)) flight.TrySetResult(result);
        }
    }

    private void CompleteProjectionException(ProjectionNode node, Exception error)
    {
        lock (this)
        {
            // Stored, never published: every later observer rethrows it before it could start.
            node.Exception = ExceptionDispatchInfo.Capture(error);
            var flight = node.Flight!;
            node.Flight = null;
            node.Project = null;
            node.ProjectAsync = null;
            if (ReferenceEquals(flight, ProjectionNode.UnjoinedFlight)) return;
            if (error is OperationCanceledException cancelled)
                flight.TrySetCanceled(cancelled.CancellationToken);
            else
                flight.TrySetException(error);
        }
    }

    internal EvalResult<Evaluator.CountedResult> Demand()
    {
        _token.ThrowIfCancellationRequested();
        var terminal = _budget?.CheckContinuation();
        lock (this)
        {
            if (terminal is not null)
                return _completed is { IsError: true } failed && failed.Error.IsResourceLimit ? failed : terminal;
            if (_completed is { } cached) return cached;
            _exception?.Throw();
        }
        // META-S3-0b: a non-initiating observation never starts (or joins) a VALUE flight; it
        // reads the outcome its resolution recorded, or reports this VALUE pending.
        if (t_observation is { } observation) return observation.ObserveValue(this);
        var parent = Current.Value;
        if (!AddDependency(parent))
            return new EvalError.DemandCycle { Span = Span };
        try
        {
            Task<EvalResult<Evaluator.CountedResult>>? task;
            lock (this)
            {
                if (_completed is { } completed) return completed;
                _exception?.Throw();
                task = JoinOrStartFlight();
            }
            if (task is null)
            {
                var outer = EnterComputation(this, out var inner);
                try { Complete(RuntimeHelpers.TryEnsureSufficientExecutionStack()
                    ? _suspension is not null ? Evaluator.EvalSuspendedValue(this, _suspension) : _evaluate!()
                    : new EvalError.EvaluationStackExhausted { Span = Span }); }
                catch (Exception error) { CompleteException(error); }
                finally { LeaveComputation(parent, outer, inner); }
                return StarterOutcome();
            }
            try { return task.GetAwaiter().GetResult(); }
            catch
            {
                // A cancelled completion task synthesizes TaskCanceledException.
                // Preserve the original host exception and token at the language boundary.
                lock (this) _exception?.Throw();
                throw;
            }
        }
        finally { RemoveDependency(parent); }
    }

    internal async ValueTask<EvalResult<Evaluator.CountedResult>> DemandAsync()
    {
        _token.ThrowIfCancellationRequested();
        var terminal = _budget?.CheckContinuation();
        lock (this)
        {
            if (terminal is not null)
                return _completed is { IsError: true } failed && failed.Error.IsResourceLimit ? failed : terminal;
            if (_completed is { } cached) return cached;
            _exception?.Throw();
        }
        ThrowIfInitiatingWhileObserving();
        var parent = Current.Value;
        if (!AddDependency(parent))
            return new EvalError.DemandCycle { Span = Span };
        try
        {
            Task<EvalResult<Evaluator.CountedResult>>? task;
            lock (this)
            {
                if (_completed is { } completed) return completed;
                _exception?.Throw();
                task = JoinOrStartFlight();
            }
            if (task is null)
            {
                await EvaluateAsync().ConfigureAwait(false);
                return StarterOutcome();
            }
            try { return await task.ConfigureAwait(false); }
            catch
            {
                lock (this) _exception?.Throw();
                throw;
            }
        }
        finally { RemoveDependency(parent); }
    }

    private async ValueTask EvaluateAsync()
    {
        // TWIN-ONLY (intentional difference from the synchronous Demand): see StackHop.
        if (StackHop.HostStackIsLow()) await new StackHop();
        var previous = Current.Value;
        var outer = EnterComputation(this, out var inner);
        try { Complete(RuntimeHelpers.TryEnsureSufficientExecutionStack()
            ? _suspension is not null
                ? await Evaluator.EvalSuspendedValueAsync(this, _suspension).ConfigureAwait(false)
                : await _evaluateAsync!().ConfigureAwait(false)
            : new EvalError.EvaluationStackExhausted { Span = Span }); }
        catch (Exception error) { CompleteException(error); }
        finally { LeaveComputation(previous, outer, inner); }
    }

    // Under the gate, with no outcome yet: starts the VALUE flight (null: the caller computes) or
    // joins it, creating the shared completion when this is its first joiner.
    private Task<EvalResult<Evaluator.CountedResult>>? JoinOrStartFlight()
    {
        if (_flight is null)
        {
            _flight = UnjoinedFlight;
            return null;
        }
        if (ReferenceEquals(_flight, UnjoinedFlight))
            _flight = new(TaskCreationOptions.RunContinuationsAsynchronously);
        return _flight.Task;
    }

    // The starter's outcome once its computation has ended: exactly what awaiting the shared
    // completion delivers (the memo, or the stored exception rethrown, as a joiner's catch does).
    // The computation wrote it before this read and nothing rewrites it.
    private EvalResult<Evaluator.CountedResult> StarterOutcome()
    {
        if (_completed is { } completed) return completed;
        _exception!.Throw();
        throw new System.Diagnostics.UnreachableException();
    }

    private void Complete(EvalResult<Evaluator.CountedResult> result)
    {
        if (result.IsError && result.Error.IsResourceLimit) _budget?.RetainTerminal(result.Error);
        lock (this)
        {
            // Published with the completion, as CompleteProjection does: every later observer
            // reads the memo first, so the released completion and computation are never needed
            // again; a joined observer awaits its own copy of the task.
            _completed = result;
            _evaluate = null;
            _evaluateAsync = null;
            var flight = _flight!;
            _flight = null;
            if (!ReferenceEquals(flight, UnjoinedFlight)) flight.TrySetResult(result);
        }
    }

    private void CompleteException(Exception error)
    {
        lock (this)
        {
            // Stored, never published: every later observer rethrows it before it could start.
            _exception = ExceptionDispatchInfo.Capture(error);
            _evaluate = null;
            _evaluateAsync = null;
            var flight = _flight!;
            _flight = null;
            if (ReferenceEquals(flight, UnjoinedFlight)) return;
            if (error is OperationCanceledException cancelled)
                flight.TrySetCanceled(cancelled.CancellationToken);
            else
                flight.TrySetException(error);
        }
    }

    /// <summary>
    /// Whether the current logical flow is running INSIDE this cell's VALUE evaluation: the flow's
    /// current node is this cell, or a node this cell's evaluation is (transitively) waiting on
    /// through its wait-for edges. It evaluates nothing. An invocation plan whose supply is being
    /// prepared by this cell's VALUE reads it to report a re-entrant preparation as
    /// <see cref="EvalError.DemandCycle"/> instead of waiting on itself (S0).
    /// </summary>
    internal bool IsEvaluatingInCurrentFlow() => IsActiveInCurrentFlow();
}
