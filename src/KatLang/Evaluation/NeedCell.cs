using System.Runtime.ExceptionServices;
using System.Runtime.CompilerServices;

namespace KatLang.Evaluation;

/// <summary>
/// One invocation's supplied computation. VALUE completion and CALLABLE identity are
/// independent; transport shares this object. No demand bookkeeping is a language step.
/// </summary>
internal sealed class NeedCell
{
    private static readonly object DependencyGate = new();
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
            return _callable ??= _project?.Invoke() ?? EvalResult<Algorithm?>.Ok(null);
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
                    ? _evaluate!() : new EvalError.EvaluationStackExhausted { Span = Span }); }
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
            ? await _evaluateAsync!().ConfigureAwait(false) : new EvalError.EvaluationStackExhausted { Span = Span }); }
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
    private bool AddDependency(NeedCell? parent)
    {
        if (parent is null) return true;
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

    private void RemoveDependency(NeedCell? parent)
    {
        if (parent is null) return;
        lock (DependencyGate)
        {
            var count = parent._dependencies![this];
            if (count == 1) parent._dependencies!.Remove(this);
            else parent._dependencies![this] = count - 1;
        }
    }
}
