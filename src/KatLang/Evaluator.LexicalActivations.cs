using System.Runtime.CompilerServices;

namespace KatLang;

public static partial class Evaluator
{
    // A binding belongs to one activation of its lexical owner. Keeping the three
    // channels together prevents a shadowing caller from supplying any missing channel.
    // Weak metadata is runtime-only; it neither changes public record equality nor
    // participates in the exported property's declaration-scoped cache key.
    private sealed record ParameterActivation(
        IReadOnlyList<(string, Result)> Values,
        IReadOnlyList<(string Name, Algorithm Value, EvalError? ValueError)> Algorithms,
        IReadOnlyList<(string Name, CountedResult Value)> Counted);

    private static readonly ConditionalWeakTable<Algorithm, ParameterActivation> AlgorithmActivations = new();
    private static readonly ConditionalWeakTable<ScopeCtx, ParameterActivation> ScopeActivations = new();
    private static readonly ConditionalWeakTable<Algorithm, object> AlgorithmDeclarations = new();

    private static object DeclarationIdentity(Algorithm algorithm)
        => AlgorithmDeclarations.GetValue(algorithm, static _ => new object());

    private static Algorithm PreserveDeclarationIdentity(Algorithm original, Algorithm wired)
    {
        AlgorithmDeclarations.Add(wired, DeclarationIdentity(original));
        return wired;
    }

    internal static EvalCtx EnterAlgorithmBody(Algorithm algorithm, EvalCtx ctx, IReadOnlyList<(string, Result)> values)
    {
        if (algorithm.Params.Count == 0)
            return ctx.Push(algorithm);

        var active = PreserveDeclarationIdentity(algorithm, algorithm with { });
        AlgorithmActivations.Add(active, SnapshotParameters(algorithm.Params, ctx, values));
        return ctx.Push(active);
    }

    private static ParameterActivation SnapshotParameters(IReadOnlyList<string> names, EvalCtx ctx,
        IReadOnlyList<(string Name, Result Value)> values)
    {
        var owned = new HashSet<string>(names, StringComparer.Ordinal);
        return new(
            values.Where(binding => owned.Contains(binding.Name)).DistinctBy(binding => binding.Name).ToArray(),
            ctx.AlgEnv.Where(binding => owned.Contains(binding.Name)).DistinctBy(binding => binding.Name).ToArray(),
            ctx.CountedParamEnv.Where(binding => owned.Contains(binding.Name)).DistinctBy(binding => binding.Name).ToArray());
    }

    private static ScopeCtx ScopeInContext(Algorithm algorithm, EvalCtx ctx)
    {
        var scope = AsScopeCtx(algorithm);
        if (ScopeActivations.TryGetValue(scope, out _) || ctx.Head is not { } site)
            return scope;

        // Static navigation may name the declaration of a currently active lexical
        // ancestor. Use that ancestor, never a dynamically live unrelated caller.
        for (var level = AsScopeCtx(site); level is not null; level = level.Parent)
        {
            if (IsSameDeclaringScope(scope, level) && CompatibleActivations(scope, level))
                return level;
        }

        return scope;
    }

    private static bool CompatibleActivations(ScopeCtx? required, ScopeCtx? actual)
    {
        while (required is not null && actual is not null)
        {
            if (ScopeActivations.TryGetValue(required, out var expected)
                && (!ScopeActivations.TryGetValue(actual, out var found) || !ReferenceEquals(expected, found)))
                return false;
            required = required.Parent;
            actual = actual.Parent;
        }
        return required is null && actual is null;
    }

    private static Algorithm ChildOfInContext(Algorithm parent, Algorithm child, EvalCtx ctx)
        => WithParent(child, ScopeInContext(parent, ctx));

    private static ParameterActivation? CapturedParameterActivation(string name, EvalCtx ctx)
    {
        if (ctx.Head is not { } site || site.Params.Contains(name, StringComparer.Ordinal))
            return null;

        var owner = site.Parent is { } parent ? RequiredParameterOwner(parent, name) : null;
        return owner is not null && ScopeActivations.TryGetValue(owner, out var activation)
            ? activation
            : null;
    }

    private static EvalCtx ParameterContext(string name, EvalCtx ctx, ref IReadOnlyList<(string, Result)> values)
    {
        if (CapturedParameterActivation(name, ctx) is not { } activation)
            return ctx;

        values = activation.Values;
        return ctx.WithAlgEnv(activation.Algorithms).WithCountedParamEnv(activation.Counted);
    }

    private static bool ParameterHasValue(string name, EvalCtx ctx, IReadOnlyList<(string, Result)> values)
    {
        var parameterCtx = ParameterContext(name, ctx, ref values);
        return LookupCountedParam(parameterCtx.CountedParamEnv, name) is not null || LookupVal(values, name) is not null;
    }

    internal static bool CapturedParameterNeedsOwnerLookup(string name, EvalCtx ctx, IReadOnlyList<(string, Result)> values)
    {
        if (CapturedParameterActivation(name, ctx) is not { } activation)
            return false;
        return LookupCountedParam(activation.Counted, name) != LookupCountedParam(ctx.CountedParamEnv, name)
            || !ReferenceEquals(LookupVal(activation.Values, name), LookupVal(values, name))
            || LookupAlgBinding(activation.Algorithms, name) != LookupAlgBinding(ctx.AlgEnv, name);
    }
}
