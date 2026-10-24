using System.Runtime.CompilerServices;

namespace KatLang.Evaluation.Caching;

/// <summary>
/// Identifies one shared bind of an assignment-deconstruction group. A deconstruction
/// <c>x0, ..., x{N-1} = RHS</c> elaborates to N target properties that each apply the SAME shared
/// N-capture pattern to the SAME hoisted <c>$deconstruct$</c> source, so demanding every target
/// formerly rebound the whole pattern N times (O(N^2)). Binding the pattern is a pure function of
/// the pattern and the source value, so a bind may be shared by exactly the helpers whose ORDINARY
/// bind would bind the same pattern to the same source value (DECON-CACHE-2, October 2026; the
/// DECON-CACHE-1 research's host witnesses showed that the former group/owner/reader key alone
/// served wrong values after public record transformations):
/// <list type="bullet">
///   <item><see cref="GroupIdentity"/> — the per-deconstruction token the parser mints and every
///   target helper carries (it also scopes the group-wide re-entry guard below);</item>
///   <item><see cref="PatternIdentity"/> — the helper's ACTUAL parameter-pattern list, by reference.
///   The group token survives a host <c>with</c> copy that replaces the unpacking pattern, so the token
///   alone no longer names one pattern; the parser's helpers of one group share one list (an import
///   view rewrites that list once, preserving the sharing);</item>
///   <item><see cref="OwnerIdentity"/> and <see cref="ValueEnvironmentIdentity"/> — the caller's
///   structural scope identity (<see cref="StructuralOwnerIdentity"/>: rebuilt caller records keep
///   sharing) and the READER's binding context (<c>Evaluator.BindingContextIdentity</c>), the
///   conservative per-consumer dimensions the memo has always had, kept unchanged;</item>
///   <item><see cref="SourceKey"/> — the COMPLETE property-cache key of the source entry the helper's
///   one argument actually reads (<see cref="ZeroArgPropertyCacheKey"/>: declaring owner — an ownerless
///   host <see cref="ScopeCtx"/> by reference —, declaration, binding, declaring activation of a
///   local-only source, run), found by the evaluator's own lexical lookup from the caller, so a
///   locally shadowed source, a different argument, ownerless host scopes over one property list and
///   two declarations sharing a list never merge.</item>
/// </list>
/// Every component compares by identity (references, or the structural identities' own equality),
/// never by a diagnostic hash. No run identity is needed beyond the source key's: a
/// <see cref="RunScopedDeconstructionBindingCache"/> is constructed inside the evaluator's root
/// context and is never host-supplied, so one instance can never span two runs.
/// </summary>
internal readonly record struct DeconstructionBindingExecution(
    object GroupIdentity,
    object PatternIdentity,
    object OwnerIdentity,
    object ValueEnvironmentIdentity,
    ZeroArgPropertyCacheKey SourceKey);

/// <summary>
/// Run-scoped memoization of assignment-deconstruction binds. The first demanded target of a
/// group performs the full bind once and stores its bound cells by binding name; every later
/// target with the same <see cref="DeconstructionBindingExecution"/> projects the cell its own
/// output names in O(1). The counted and non-counted helper results are both a value boundary over
/// the same value, so the bound cell is all that must be retained.
/// </summary>
internal interface IDeconstructionBindingCache
{
    /// <summary>
    /// Returns the bound cells (by binding name) for this deconstruction group and binding
    /// context, computing them via <paramref name="bind"/> only on a miss. Errors are NEVER
    /// stored (consistent with <see cref="IZeroArgPropertyResultCache"/>): a deterministic
    /// binding failure recurs identically, and a reached resource limit is already terminal for
    /// the run (`EvaluationBudget.RetainTerminal`), so nothing could read a stored one. The
    /// evaluator passes only executions whose source read obtains the source's PUBLISHED value
    /// (<see cref="IZeroArgPropertyResultCache.ReadObtainsPublishedValue"/>); every other helper
    /// binds without consulting the memo.
    /// </summary>
    EvalResult<IReadOnlyDictionary<string, NeedCell>> GetOrBind(
        DeconstructionBindingExecution execution,
        Func<EvalResult<IReadOnlyDictionary<string, NeedCell>>> bind);

    /// <summary>
    /// Async twin of <see cref="GetOrBind"/>, used only by the evaluator's async twin
    /// family (whose bind callback awaits async twin evaluation). Same store, same keys,
    /// same never-store-errors rule: one run uses exactly one of the two members
    /// throughout, and both implementations below are run-scoped, so the shared-bind
    /// semantics are unchanged. This interface is internal and never host-supplied, so
    /// the member carries no public-surface cost.
    /// </summary>
    ValueTask<EvalResult<IReadOnlyDictionary<string, NeedCell>>> GetOrBindAsync(
        DeconstructionBindingExecution execution,
        Func<ValueTask<EvalResult<IReadOnlyDictionary<string, NeedCell>>>> bind);
}

internal sealed class DeconstructionBindingCacheKeyComparer : IEqualityComparer<DeconstructionBindingExecution>
{
    public static DeconstructionBindingCacheKeyComparer Instance { get; } = new();

    private DeconstructionBindingCacheKeyComparer()
    {
    }

    public bool Equals(DeconstructionBindingExecution x, DeconstructionBindingExecution y)
        => ReferenceEquals(x.GroupIdentity, y.GroupIdentity)
            && ReferenceEquals(x.PatternIdentity, y.PatternIdentity)
            && ZeroArgPropertyCacheKeyComparer.OwnerIdentityEquals(x.OwnerIdentity, y.OwnerIdentity)
            && ReferenceEquals(x.ValueEnvironmentIdentity, y.ValueEnvironmentIdentity)
            && ZeroArgPropertyCacheKeyComparer.Instance.Equals(x.SourceKey, y.SourceKey);

    public int GetHashCode(DeconstructionBindingExecution obj)
    {
        var hash = new HashCode();
        hash.Add(RuntimeHelpers.GetHashCode(obj.GroupIdentity));
        hash.Add(RuntimeHelpers.GetHashCode(obj.PatternIdentity));
        hash.Add(obj.OwnerIdentity is StructuralOwnerIdentity owner
            ? owner.GetHashCode()
            : RuntimeHelpers.GetHashCode(obj.OwnerIdentity));
        hash.Add(RuntimeHelpers.GetHashCode(obj.ValueEnvironmentIdentity));
        hash.Add(ZeroArgPropertyCacheKeyComparer.Instance.GetHashCode(obj.SourceKey));
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

    public EvalResult<IReadOnlyDictionary<string, NeedCell>> GetOrBind(
        DeconstructionBindingExecution execution,
        Func<EvalResult<IReadOnlyDictionary<string, NeedCell>>> bind)
        => bind();

    public ValueTask<EvalResult<IReadOnlyDictionary<string, NeedCell>>> GetOrBindAsync(
        DeconstructionBindingExecution execution,
        Func<ValueTask<EvalResult<IReadOnlyDictionary<string, NeedCell>>>> bind)
        => bind();
}

/// <summary>
/// The run-scoped shared-bind memo. It adds no semantics only while every bind it serves was computed
/// from the hoisted source's PUBLISHED value by the very pattern the reading helper binds. THE STORE
/// INVARIANT (DECON-CACHE-2): a completed bind is stored only when (1) the evaluator admitted its
/// execution — the source read that supplies it obtains the published value of exactly
/// <see cref="DeconstructionBindingExecution.SourceKey"/>, decided before the bind starts from the lookup
/// that read itself performs, with no extra read (<c>Evaluator.SharedDeconstructionBind</c>); (2) it
/// succeeded; and (3) no other bind of its GROUP was running when it started. A stored bind is never
/// replaced. (3) is the group-wide re-entry guard kept from Q-37: a target read again while its group
/// is still binding gets its own, unstored bind. With (1) in force it is no longer what keeps an
/// intermediate source value out of the memo — a re-entrant source read fails (1) — but it still keeps
/// every bind started inside a running bind of its group (recursive owners, re-entrant targets) out of
/// the memo, which is the established bind and step accounting of such programs (R12's seven binds,
/// pinned by <c>DeconstructionMemoEligibilityTests</c>); narrowing it to the full key is an accounting
/// change that needs its own decision. Programs that never re-enter a deconstruction keep every hit
/// they had before.
/// </summary>
internal sealed class RunScopedDeconstructionBindingCache : IDeconstructionBindingCache
{
    private readonly Dictionary<DeconstructionBindingExecution, IReadOnlyDictionary<string, NeedCell>> _results =
        new(DeconstructionBindingCacheKeyComparer.Instance);

    // Group identity -> number of its binds currently running (absent when none).
    private readonly Dictionary<object, int> _runningBinds = new(ReferenceEqualityComparer.Instance);

    /// <summary>Number of stored binds.</summary>
    internal int Count => _results.Count;

    /// <summary>Number of groups with a bind still running (zero between accesses).</summary>
    internal int RunningGroupCount => _runningBinds.Count;

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

    public EvalResult<IReadOnlyDictionary<string, NeedCell>> GetOrBind(
        DeconstructionBindingExecution execution,
        Func<EvalResult<IReadOnlyDictionary<string, NeedCell>>> bind)
    {
        if (_results.TryGetValue(execution, out var cached))
            return EvalResult<IReadOnlyDictionary<string, NeedCell>>.Ok(cached);

        var nested = EnterBind(execution.GroupIdentity);
        EvalResult<IReadOnlyDictionary<string, NeedCell>> result;
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

        // A bind nested in a running bind of its group is never stored (the group-wide guard).
        if (!nested)
            _results.TryAdd(execution, result.Value);
        return result;
    }

    /// <summary>
    /// MIRROR OF <see cref="GetOrBind"/> — keep in lock-step: same key, same store,
    /// same nested-bind rule, same never-store-errors rule. One run drives evaluation through exactly one of the
    /// sync/async evaluator families, and within the async family each bind is awaited
    /// before evaluation continues, so the dictionary is never touched concurrently.
    /// </summary>
    public async ValueTask<EvalResult<IReadOnlyDictionary<string, NeedCell>>> GetOrBindAsync(
        DeconstructionBindingExecution execution,
        Func<ValueTask<EvalResult<IReadOnlyDictionary<string, NeedCell>>>> bind)
    {
        if (_results.TryGetValue(execution, out var cached))
            return EvalResult<IReadOnlyDictionary<string, NeedCell>>.Ok(cached);

        var nested = EnterBind(execution.GroupIdentity);
        EvalResult<IReadOnlyDictionary<string, NeedCell>> result;
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
            _results.TryAdd(execution, result.Value);
        return result;
    }
}
