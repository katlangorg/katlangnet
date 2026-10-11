using System.Runtime.CompilerServices;

namespace KatLang.Evaluation.Caching;

/// <summary>
/// Identifies one shared bind of an assignment-deconstruction group in one binding context.
/// A deconstruction <c>x0, ..., x{N-1} = RHS</c> elaborates to N target properties that each
/// apply the SAME shared N-capture pattern to the SAME hoisted <c>$deconstruct$</c> source, so
/// demanding every target formerly rebound the whole pattern N times (O(N^2)). Binding the
/// pattern is a pure function of the shared pattern and the source value. The group identity is
/// a stable per-deconstruction token shared by its N target helpers.
///
/// <para>The source value is NOT a function of the environments alone: the helper's argument is
/// <c>Resolve("$deconstruct$N")</c>, evaluated in the CALLER's lexical context, so it depends on
/// the owning scope as well. The public AST is host-constructible with shared (acyclic) subtrees,
/// so one parser-elaborated group can be placed under two different owners that resolve that
/// hoisted source differently; keying without the owner returned the first owner's bound values
/// for the second. <see cref="OwnerIdentity"/> closes that, exactly as
/// <see cref="ZeroArgPropertyCacheKey"/> does for structural property access — and for the same
/// reason it is a <see cref="StructuralOwnerIdentity"/> (empty scope components compare as
/// resolution-equivalent; non-empty components compare by reference) rather than the owner
/// reference: the evaluator rebuilds the caller record for every demanded target, so keying on
/// the reference would restore the O(N^2) rebind this cache exists to prevent.</para>
///
/// <para>No run identity is carried, unlike the zero-argument property cache: a
/// <see cref="RunScopedDeconstructionBindingCache"/> is constructed inside the evaluator's root
/// context and is never host-supplied, so one instance can never span two runs.</para>
/// </summary>
internal readonly record struct DeconstructionBindingExecution(
    object GroupIdentity,
    object OwnerIdentity,
    object ValueEnvironmentIdentity,
    object AlgorithmEnvironmentIdentity,
    object CountedParamEnvironmentIdentity);

/// <summary>
/// Run-scoped memoization of assignment-deconstruction binds. The first demanded target of a
/// group performs the full N-capture bind once and stores the ordered per-target demand cells;
/// every later target of the same group in the same binding context projects its own slot in
/// O(1). The stored list is the shared bind's demand cells in target order (capture order); the
/// counted and non-counted helper results are both a value boundary over the same value, so the
/// per-target value is all that must be retained.
/// </summary>
internal interface IDeconstructionBindingCache
{
    /// <summary>
    /// Returns the ordered per-target demand cells for this deconstruction group and binding
    /// context, computing them via <paramref name="bind"/> only on a miss. Errors are NEVER
    /// stored (consistent with <see cref="IZeroArgPropertyResultCache"/>): a deterministic
    /// binding failure recurs identically, and a reached resource limit is already terminal for
    /// the run (`EvaluationBudget.RetainTerminal`), so nothing could read a stored one.
    /// </summary>
    EvalResult<IReadOnlyList<NeedCell>> GetOrBind(
        DeconstructionBindingExecution execution,
        Func<EvalResult<IReadOnlyList<NeedCell>>> bind);

    /// <summary>
    /// Async twin of <see cref="GetOrBind"/>, used only by the evaluator's async twin
    /// family (whose bind callback awaits async twin evaluation). Same store, same keys,
    /// same never-store-errors rule: one run uses exactly one of the two members
    /// throughout, and both implementations below are run-scoped, so the shared-bind
    /// semantics are unchanged. This interface is internal and never host-supplied, so
    /// the member carries no public-surface cost.
    /// </summary>
    ValueTask<EvalResult<IReadOnlyList<NeedCell>>> GetOrBindAsync(
        DeconstructionBindingExecution execution,
        Func<ValueTask<EvalResult<IReadOnlyList<NeedCell>>>> bind);
}

internal readonly record struct DeconstructionBindingCacheKey(
    object GroupIdentity,
    object OwnerIdentity,
    object ValueEnvironmentIdentity,
    object AlgorithmEnvironmentIdentity,
    object CountedParamEnvironmentIdentity);

internal sealed class DeconstructionBindingCacheKeyComparer : IEqualityComparer<DeconstructionBindingCacheKey>
{
    public static DeconstructionBindingCacheKeyComparer Instance { get; } = new();

    private DeconstructionBindingCacheKeyComparer()
    {
    }

    public bool Equals(DeconstructionBindingCacheKey x, DeconstructionBindingCacheKey y)
        => ReferenceEquals(x.GroupIdentity, y.GroupIdentity)
            && ZeroArgPropertyCacheKeyComparer.OwnerIdentityEquals(x.OwnerIdentity, y.OwnerIdentity)
            && ReferenceEquals(x.ValueEnvironmentIdentity, y.ValueEnvironmentIdentity)
            && ReferenceEquals(x.AlgorithmEnvironmentIdentity, y.AlgorithmEnvironmentIdentity)
            && ReferenceEquals(x.CountedParamEnvironmentIdentity, y.CountedParamEnvironmentIdentity);

    public int GetHashCode(DeconstructionBindingCacheKey obj)
    {
        var hash = new HashCode();
        hash.Add(RuntimeHelpers.GetHashCode(obj.GroupIdentity));
        hash.Add(obj.OwnerIdentity is StructuralOwnerIdentity owner
            ? owner.GetHashCode()
            : RuntimeHelpers.GetHashCode(obj.OwnerIdentity));
        hash.Add(RuntimeHelpers.GetHashCode(obj.ValueEnvironmentIdentity));
        hash.Add(RuntimeHelpers.GetHashCode(obj.AlgorithmEnvironmentIdentity));
        hash.Add(RuntimeHelpers.GetHashCode(obj.CountedParamEnvironmentIdentity));
        return hash.ToHashCode();
    }
}

/// <summary>
/// No-op cache: every access rebinds. Used by the default empty context, which shares the
/// uncached zero-argument property cache; correctness is preserved (each target simply pays its
/// own bind), only the O(N^2) reuse benefit is absent.
/// </summary>
internal sealed class UncachedDeconstructionBindingCache : IDeconstructionBindingCache
{
    public static UncachedDeconstructionBindingCache Instance { get; } = new();

    private UncachedDeconstructionBindingCache()
    {
    }

    public EvalResult<IReadOnlyList<NeedCell>> GetOrBind(
        DeconstructionBindingExecution execution,
        Func<EvalResult<IReadOnlyList<NeedCell>>> bind)
        => bind();

    public ValueTask<EvalResult<IReadOnlyList<NeedCell>>> GetOrBindAsync(
        DeconstructionBindingExecution execution,
        Func<ValueTask<EvalResult<IReadOnlyList<NeedCell>>>> bind)
        => bind();
}

/// <summary>
/// The run-scoped shared-bind memo. It adds no semantics only while every bind it serves was computed
/// from the hoisted source's PUBLISHED value. Since Q-37 (the outermost property-style evaluation owns
/// the cache entry, <see cref="ZeroArgPropertyPublications"/>) a re-entrant read of the source — a
/// target of the group read again while the source's owning evaluation is still running — evaluates
/// an INTERMEDIATE source value that is never published, and such a read always happens inside
/// another, still-running bind of the SAME group (only the group's target helpers read its source).
/// So a bind that starts while another bind of its group is running is not stored, and a stored bind
/// is never replaced: a re-entrant target read gets its own bind, exactly as the reference semantics
/// (one bind per target read; Lean has no such memo) requires. Programs that never re-enter a
/// deconstruction keep every hit they had before.
/// </summary>
internal sealed class RunScopedDeconstructionBindingCache : IDeconstructionBindingCache
{
    private readonly Dictionary<DeconstructionBindingCacheKey, IReadOnlyList<NeedCell>> _results =
        new(DeconstructionBindingCacheKeyComparer.Instance);

    // Group identity -> number of its binds currently running (absent when none).
    private readonly Dictionary<object, int> _runningBinds = new(ReferenceEqualityComparer.Instance);

    private bool EnterBind(object group)
    {
        _runningBinds.TryGetValue(group, out var running);
        _runningBinds[group] = running + 1;
        return running > 0;
    }

    private void ExitBind(object group)
    {
        var running = _runningBinds[group] - 1;
        if (running == 0)
            _runningBinds.Remove(group);
        else
            _runningBinds[group] = running;
    }

    public EvalResult<IReadOnlyList<NeedCell>> GetOrBind(
        DeconstructionBindingExecution execution,
        Func<EvalResult<IReadOnlyList<NeedCell>>> bind)
    {
        var key = new DeconstructionBindingCacheKey(
            execution.GroupIdentity,
            execution.OwnerIdentity,
            execution.ValueEnvironmentIdentity,
            execution.AlgorithmEnvironmentIdentity,
            execution.CountedParamEnvironmentIdentity);

        if (_results.TryGetValue(key, out var cached))
            return EvalResult<IReadOnlyList<NeedCell>>.Ok(cached);

        var nested = EnterBind(execution.GroupIdentity);
        EvalResult<IReadOnlyList<NeedCell>> result;
        try
        {
            result = bind();
        }
        finally
        {
            ExitBind(execution.GroupIdentity);
        }

        if (result.IsError)
            return result.Error;

        // A bind nested in a running bind of its group may have read an intermediate source (Q-37).
        if (!nested)
            _results.TryAdd(key, result.Value);
        return result;
    }

    /// <summary>
    /// MIRROR OF <see cref="GetOrBind"/> — keep in lock-step: same key derivation, same store,
    /// same nested-bind rule, same never-store-errors rule. One run drives evaluation through exactly one of the
    /// sync/async evaluator families, and within the async family each bind is awaited
    /// before evaluation continues, so the dictionary is never touched concurrently.
    /// </summary>
    public async ValueTask<EvalResult<IReadOnlyList<NeedCell>>> GetOrBindAsync(
        DeconstructionBindingExecution execution,
        Func<ValueTask<EvalResult<IReadOnlyList<NeedCell>>>> bind)
    {
        var key = new DeconstructionBindingCacheKey(
            execution.GroupIdentity,
            execution.OwnerIdentity,
            execution.ValueEnvironmentIdentity,
            execution.AlgorithmEnvironmentIdentity,
            execution.CountedParamEnvironmentIdentity);

        if (_results.TryGetValue(key, out var cached))
            return EvalResult<IReadOnlyList<NeedCell>>.Ok(cached);

        var nested = EnterBind(execution.GroupIdentity);
        EvalResult<IReadOnlyList<NeedCell>> result;
        try
        {
            result = await bind().ConfigureAwait(false);
        }
        finally
        {
            ExitBind(execution.GroupIdentity);
        }

        if (result.IsError)
            return result.Error;

        if (!nested)
            _results.TryAdd(key, result.Value);
        return result;
    }
}
