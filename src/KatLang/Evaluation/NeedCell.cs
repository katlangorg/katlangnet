using System.Runtime.ExceptionServices;
using System.Runtime.CompilerServices;

namespace KatLang.Evaluation;

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
///   are sticky; and the completed outcome is never rewritten.</item>
///   <item><b>The per-cell gate</b> (<c>_gate</c>) guards the cell's own state. It is held only for
///   field updates and for the CALLABLE projection, which is identity-only resolution: it
///   evaluates nothing and demands no VALUE.</item>
///   <item><b>The wait-for graph</b> (the <c>_dependencies</c> edges, NEED-09) belongs to the run: its
///   gate is the run budget's <see cref="EvaluationBudget.NeedDependencyGate"/>. A cycle is detected
///   before its closing edge is awaited, across overlapping async chains too. Independent runs
///   never contend for one gate. The graph lock is never held while user code runs or a flight is
///   awaited, and the two gates are never nested.</item>
///   <item><b>Cleanup.</b> An edge exists exactly while its demand frame is active. It is removed on
///   every exit: success, failure, exception, cancellation or a cycle.</item>
///   <item><b>Cells without a budget.</b> A Ready cell carries no budget but never joins a graph: it
///   is complete before any edge is considered, and it is never a demand's parent. A suspended cell
///   without a budget, which only a test builds, shares one process-wide fallback graph.</item>
/// </list>
/// </summary>
internal sealed class NeedCell
{
    // The graph gate of suspended cells that belong to no run: only a test builds one (see
    // AddDependency). A Ready cell has no budget either, but it never takes part in an edge.
    private static readonly Lock UnownedDependencyGate = new();
    // The cell whose evaluation the current logical flow is running: a demand's parent.
    private static readonly AsyncLocal<NeedCell?> Current = new();
    private readonly object _gate = new();
    private readonly CancellationToken _token;
    private readonly bool _ready;
    private readonly EvaluationBudget? _budget;
    private Func<EvalResult<Evaluator.CountedResult>>? _evaluate;
    private Func<ValueTask<EvalResult<Evaluator.CountedResult>>>? _evaluateAsync;
    private readonly Func<EvalResult<Algorithm?>>? _project;
    private Dictionary<NeedCell, int>? _dependencies;
    private TaskCompletionSource<EvalResult<Evaluator.CountedResult>>? _flight;
    private EvalResult<Evaluator.CountedResult>? _completed;
    private ExceptionDispatchInfo? _exception;
    private EvalResult<Algorithm?>? _callable;
    // A written argument's suspension (Lean `NeedSuspension.expression source caller values`),
    // kept as DATA rather than as closures over it. It is never cleared: CALLABLE projection may
    // run after VALUE completion, and an invocation plan executes over it again (S0).
    private readonly Evaluator.ExpressionSuspension? _suspension;

    internal NeedCell(
        Func<EvalResult<Evaluator.CountedResult>> evaluate,
        Func<ValueTask<EvalResult<Evaluator.CountedResult>>> evaluateAsync,
        Func<EvalResult<Algorithm?>>? project = null,
        SourceSpan? span = null,
        IReadOnlyList<NeedCell>? slice = null,
        Expr? source = null,
        EvaluationBudget? budget = null,
        CancellationToken token = default)
    {
        _evaluate = evaluate;
        _evaluateAsync = evaluateAsync;
        _project = project;
        _token = token;
        _budget = budget;
        Span = span;
        Slice = slice;
        Source = source;
    }

    /// <summary>
    /// A written argument's cell (<see cref="Evaluator.SupplyCell"/>): its VALUE, async VALUE and
    /// CALLABLE projection are the evaluator's static operations over <paramref name="suspension"/>,
    /// so the cell allocates no delegate or closure of its own.
    /// </summary>
    internal NeedCell(Expr source, Evaluator.ExpressionSuspension suspension, EvaluationBudget budget, CancellationToken token)
    {
        _suspension = suspension;
        _token = token;
        _budget = budget;
        Span = source.Span;
        Source = source;
        // An invocation plan's identity IS its one owning cell (Lean: the need address).
        if (suspension is Evaluator.InvocationPlan plan) plan.Attach(this);
    }

    /// <summary>
    /// The written argument's suspension, or <c>null</c> for a Ready, collector or host-built cell.
    /// An <see cref="Evaluator.InvocationPlan"/> suspension marks the cell as an invocation plan (S0).
    /// </summary>
    internal Evaluator.ExpressionSuspension? Suspension => _suspension;

    // Test observation only: whether this cell's VALUE has completed (successfully or not).
    internal bool HasCompletedValue
    {
        get { lock (_gate) return _completed is not null || _exception is not null; }
    }

    // Produced data is a calculation value: it never carries callable identity.
    private NeedCell(Evaluator.CountedResult value)
    {
        _ready = true;
        _completed = EvalResult<Evaluator.CountedResult>.Ok(value);
        _callable = EvalResult<Algorithm?>.Ok(null);
    }

    internal SourceSpan? Span { get; }
    internal Expr? Source { get; }
    internal IReadOnlyList<NeedCell>? Slice { get; }

    // The gate of this cell's wait-for graph: its run's (budget identity is graph identity).
    private Lock DependencyGate => _budget?.NeedDependencyGate ?? UnownedDependencyGate;

    // Test observation only: how many distinct cells this cell's evaluation currently waits on
    // (its active wait-for edges). Every edge is gone once its demand frame exits.
    internal int ActiveDependencyCount
    {
        get { lock (DependencyGate) return _dependencies?.Count ?? 0; }
    }

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
        if (_budget?.CheckContinuation() is { } terminal) return terminal;
        lock (_gate)
        {
            if (_exception?.SourceException is OperationCanceledException) _exception.Throw();
            return _callable ??= _suspension is not null
                ? Evaluator.ProjectSuspendedCallable(Source!, _suspension)
                : _project?.Invoke() ?? EvalResult<Algorithm?>.Ok(null);
        }
    }

    internal EvalResult<Evaluator.CountedResult> Demand()
    {
        _token.ThrowIfCancellationRequested();
        var terminal = _budget?.CheckContinuation();
        lock (_gate)
        {
            if (terminal is not null)
                return _completed is { IsError: true } failed && failed.Error.IsResourceLimit ? failed : terminal;
            if (_completed is { } cached) return cached;
            _exception?.Throw();
        }
        var parent = Current.Value;
        if (!AddDependency(parent))
            return new EvalError.DemandCycle { Span = Span };
        try
        {
            bool start;
            Task<EvalResult<Evaluator.CountedResult>> task;
            lock (_gate)
            {
                if (_completed is { } completed) return completed;
                _exception?.Throw();
                start = _flight is null;
                _flight ??= new(TaskCreationOptions.RunContinuationsAsynchronously);
                task = _flight.Task;
            }
            if (start)
            {
                var previous = Current.Value;
                Current.Value = this;
                try { Complete(RuntimeHelpers.TryEnsureSufficientExecutionStack()
                    ? _suspension is not null ? Evaluator.EvalSuspendedValue(this, _suspension) : _evaluate!()
                    : new EvalError.EvaluationStackExhausted { Span = Span }); }
                catch (Exception error) { CompleteException(error); }
                finally { Current.Value = previous; }
            }
            try { return task.GetAwaiter().GetResult(); }
            catch
            {
                // A cancelled completion task synthesizes TaskCanceledException.
                // Preserve the original host exception and token at the language boundary.
                lock (_gate) _exception?.Throw();
                throw;
            }
        }
        finally { RemoveDependency(parent); }
    }

    internal async ValueTask<EvalResult<Evaluator.CountedResult>> DemandAsync()
    {
        _token.ThrowIfCancellationRequested();
        var terminal = _budget?.CheckContinuation();
        lock (_gate)
        {
            if (terminal is not null)
                return _completed is { IsError: true } failed && failed.Error.IsResourceLimit ? failed : terminal;
            if (_completed is { } cached) return cached;
            _exception?.Throw();
        }
        var parent = Current.Value;
        if (!AddDependency(parent))
            return new EvalError.DemandCycle { Span = Span };
        try
        {
            bool start;
            Task<EvalResult<Evaluator.CountedResult>> task;
            lock (_gate)
            {
                if (_completed is { } completed) return completed;
                _exception?.Throw();
                start = _flight is null;
                _flight ??= new(TaskCreationOptions.RunContinuationsAsynchronously);
                task = _flight.Task;
            }
            if (start) await EvaluateAsync().ConfigureAwait(false);
            try { return await task.ConfigureAwait(false); }
            catch
            {
                lock (_gate) _exception?.Throw();
                throw;
            }
        }
        finally { RemoveDependency(parent); }
    }

    private async ValueTask EvaluateAsync()
    {
        var previous = Current.Value;
        Current.Value = this;
        try { Complete(RuntimeHelpers.TryEnsureSufficientExecutionStack()
            ? _suspension is not null
                ? await Evaluator.EvalSuspendedValueAsync(this, _suspension).ConfigureAwait(false)
                : await _evaluateAsync!().ConfigureAwait(false)
            : new EvalError.EvaluationStackExhausted { Span = Span }); }
        catch (Exception error) { CompleteException(error); }
        finally { Current.Value = previous; }
    }

    private void Complete(EvalResult<Evaluator.CountedResult> result)
    {
        if (result.IsError && result.Error.IsResourceLimit) _budget?.RetainTerminal(result.Error);
        lock (_gate)
        {
            _completed = result;
            _evaluate = null;
            _evaluateAsync = null;
            _flight!.TrySetResult(result);
        }
    }

    private void CompleteException(Exception error)
    {
        lock (_gate)
        {
            _exception = ExceptionDispatchInfo.Capture(error);
            _evaluate = null;
            _evaluateAsync = null;
            if (error is OperationCanceledException cancelled)
                _flight!.TrySetCanceled(cancelled.CancellationToken);
            else
                _flight!.TrySetException(error);
        }
    }

    // All active edges, including independently started async chains, are checked
    // atomically before waiting. Iteration bounds the host stack independently of depth.
    // The graph is PER RUN: an edge joins two cells of one budget, under that run's gate, and
    // a parent of another run records nothing. That parent is the AsyncLocal current cell
    // flowing into a run a host operation starts inside the outer evaluation; no cell of the
    // inner run can demand it, so the skipped edge closes no cycle.
    private bool AddDependency(NeedCell? parent)
    {
        if (parent is null || parent._budget != _budget) return true;
        lock (DependencyGate)
        {
            if (ReferenceEquals(this, parent)) return false;
            if (_dependencies is { Count: > 0 })
            {
                var pending = new Stack<NeedCell>();
                var visited = new HashSet<NeedCell>(ReferenceEqualityComparer.Instance);
                pending.Push(this);
                while (pending.TryPop(out var cell))
                {
                    if (ReferenceEquals(cell, parent)) return false;
                    if (!visited.Add(cell) || cell._dependencies is null) continue;
                    foreach (var dependency in cell._dependencies.Keys) pending.Push(dependency);
                }
            }
            var edges = parent._dependencies ??= new(ReferenceEqualityComparer.Instance);
            edges[this] = edges.GetValueOrDefault(this) + 1;
            return true;
        }
    }

    /// <summary>
    /// Whether the current logical flow is running INSIDE this cell's VALUE evaluation: the flow's
    /// current cell is this cell, or a cell this cell's evaluation is (transitively) waiting on
    /// through its wait-for edges. It evaluates nothing. An invocation plan whose supply is being
    /// prepared by this cell's VALUE reads it to report a re-entrant preparation as
    /// <see cref="EvalError.DemandCycle"/> instead of waiting on itself (S0).
    /// </summary>
    internal bool IsEvaluatingInCurrentFlow()
    {
        var current = Current.Value;
        if (current is null) return false;
        if (ReferenceEquals(current, this)) return true;
        if (current._budget != _budget) return false;
        lock (DependencyGate)
        {
            if (_dependencies is not { Count: > 0 }) return false;
            var pending = new Stack<NeedCell>();
            var visited = new HashSet<NeedCell>(ReferenceEqualityComparer.Instance);
            pending.Push(this);
            while (pending.TryPop(out var cell))
            {
                if (ReferenceEquals(cell, current)) return true;
                if (!visited.Add(cell) || cell._dependencies is null) continue;
                foreach (var dependency in cell._dependencies.Keys) pending.Push(dependency);
            }
            return false;
        }
    }

    private void RemoveDependency(NeedCell? parent)
    {
        if (parent is null || parent._budget != _budget) return;
        lock (DependencyGate)
        {
            var count = parent._dependencies![this];
            if (count == 1) parent._dependencies!.Remove(this);
            else parent._dependencies![this] = count - 1;
        }
    }
}
