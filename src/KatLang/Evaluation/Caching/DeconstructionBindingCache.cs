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
/// group performs the full N-capture bind once and stores the ordered per-target bound values;
/// every later target of the same group in the same binding context projects its own slot in
/// O(1). The stored list is the shared bind's bound values in target order (capture order); the
/// counted and non-counted helper results are both a value boundary over the same value, so the
/// per-target value is all that must be retained.
/// </summary>
internal interface IDeconstructionBindingCache
{
    /// <summary>
    /// Returns the ordered per-target bound values for this deconstruction group and binding
    /// context, computing them via <paramref name="bind"/> only on a miss. Errors are NEVER
    /// stored (consistent with <see cref="IZeroArgPropertyResultCache"/>): a deterministic
    /// binding failure recurs identically, and a transient resource-limit failure must be free
    /// to recur under the live budget rather than being pinned for the rest of the run.
    /// </summary>
    EvalResult<IReadOnlyList<Result>> GetOrBind(
        DeconstructionBindingExecution execution,
        Func<EvalResult<IReadOnlyList<Result>>> bind);
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

    public EvalResult<IReadOnlyList<Result>> GetOrBind(
        DeconstructionBindingExecution execution,
        Func<EvalResult<IReadOnlyList<Result>>> bind)
        => bind();
}

internal sealed class RunScopedDeconstructionBindingCache : IDeconstructionBindingCache
{
    private readonly Dictionary<DeconstructionBindingCacheKey, IReadOnlyList<Result>> _results =
        new(DeconstructionBindingCacheKeyComparer.Instance);

    public EvalResult<IReadOnlyList<Result>> GetOrBind(
        DeconstructionBindingExecution execution,
        Func<EvalResult<IReadOnlyList<Result>>> bind)
    {
        var key = new DeconstructionBindingCacheKey(
            execution.GroupIdentity,
            execution.OwnerIdentity,
            execution.ValueEnvironmentIdentity,
            execution.AlgorithmEnvironmentIdentity,
            execution.CountedParamEnvironmentIdentity);

        if (_results.TryGetValue(key, out var cached))
            return EvalResult<IReadOnlyList<Result>>.Ok(cached);

        var result = bind();
        if (result.IsError)
            return result.Error;

        _results[key] = result.Value;
        return result;
    }
}
