namespace KatLang;

/// <summary>
/// Tiny adapter over elaborated AST property scopes for front-end and editor lookup.
/// This intentionally excludes evaluator-specific runtime behavior.
/// </summary>
internal sealed class ElaboratedPropertyScope
{
    public ElaboratedPropertyScope(
        ElaboratedPropertyScope? parent,
        IReadOnlyList<Expr> opens,
        IReadOnlyList<PropertyLookupHit> properties)
    {
        Parent = parent;
        Opens = opens;
        Properties = properties;
    }

    public ElaboratedPropertyScope? Parent { get; }

    public IReadOnlyList<Expr> Opens { get; }

    public IReadOnlyList<PropertyLookupHit> Properties { get; }
}

internal readonly record struct PropertyLookupHit(Algorithm Owner, Property Property);

internal static class ElaboratedScopeLookup
{
    public static ElaboratedPropertyScope CreateScope(Algorithm algorithm, ElaboratedPropertyScope? parentOverride = null)
        => new(
            parentOverride ?? CreateParentScope(algorithm.Parent),
            algorithm.Opens,
            CreatePropertyHits(algorithm, algorithm.Properties));

    public static PropertyLookupHit? TryLookupProperty(Algorithm owner, string name)
    {
        foreach (var property in owner.Properties)
        {
            if (property.Name == name)
                return new PropertyLookupHit(owner, property);
        }

        return null;
    }

    public static PropertyLookupHit? TryLookupPublicExportedProperty(Algorithm owner, string name)
    {
        foreach (var property in owner.Properties)
        {
            if (property.Name == name
                && property.IsPublic
                && property.Exposure == PropertyExposure.Exported)
            {
                return new PropertyLookupHit(owner, property);
            }
        }

        return null;
    }

    public static PropertyLookupHit? TryLookupDirectLexicalProperty(ElaboratedPropertyScope scope, string name)
    {
        for (var current = scope; current is not null; current = current.Parent)
        {
            foreach (var hit in current.Properties)
            {
                if (hit.Property.Name == name)
                    return hit;
            }
        }

        return null;
    }

    public static Algorithm? ResolveOpenTarget(ElaboratedPropertyScope scope, Expr openExpr)
    {
        switch (openExpr)
        {
            case Expr.Resolve(var name):
                return TryLookupDirectLexicalProperty(scope, name)?.Property.Value;

            case Expr.DotCall dotCall when dotCall.IsCoreOpenForm():
            {
                var targetAlgorithm = ResolveOpenTarget(scope, dotCall.Target);
                return targetAlgorithm is null
                    ? null
                    : TryLookupPublicExportedProperty(targetAlgorithm, dotCall.Name)?.Property.Value;
            }

            case Expr.SequenceSpread(var operand):
            {
                _ = operand;
                return null;
            }

            case Expr.SequenceConstruct(var left, var right):
            {
                _ = left;
                _ = right;
                return null;
            }

            case Expr.AlgorithmExpr(var algorithm):
                return algorithm;

            case Expr.Capture:
                // RECOVERY TOLERANCE: the parser rejects capture open targets
                // (`open (M)` is a captured value, not an algorithm — the
                // evaluator's open resolution errors with BadOpenForm), so a
                // capture open reaches frontend lookup only through a
                // diagnostic-bearing recovery tree. It contributes no names —
                // an empty scope keeps recovery lookup stable without
                // pretending the capture exposes any enclosed identity.
                return new Algorithm.User(
                    Parent: null, Parameters: [], Opens: [],
                    Properties: [], Output: OutputBundle.Empty);

            default:
                return null;
        }
    }

    public static IReadOnlyList<PropertyLookupHit> LookupOpenPropertyMatches(ElaboratedPropertyScope scope, string name)
    {
        for (var current = scope; current is not null; current = current.Parent)
        {
            List<PropertyLookupHit>? hits = null;
            HashSet<string>? seenKeys = null;

            for (var i = 0; i < current.Opens.Count; i++)
            {
                var openExpr = current.Opens[i];

                // Same dedup rule as the evaluator's ResolveAllOpens (Lean:
                // resolveAllOpens): named targets are keyed by their open
                // spelling and deduplicated first-occurrence-wins, while inline
                // blocks get a unique positional key and are never deduplicated.
                // Without this, `open Lib, Lib` reported one hit per written
                // target and every name it provides looked ambiguous here while
                // the evaluator resolved it.
                seenKeys ??= [];
                if (!seenKeys.Add(OpenTargetDedupKey(openExpr, i)))
                    continue;

                var targetAlgorithm = ResolveOpenTarget(current, openExpr);
                if (targetAlgorithm is null)
                    continue;

                if (TryLookupPublicExportedProperty(targetAlgorithm, name) is { } hit)
                {
                    hits ??= [];
                    hits.Add(hit);
                }
            }

            if (hits is not null && hits.Count > 0)
                return hits;
        }

        return [];
    }

    /// <summary>
    /// Canonical dedup key for one written <c>open</c> target, matching
    /// <c>Evaluator.ResolveAllOpens</c> and Lean <c>resolveAllOpens</c>.
    /// Shared with the semantic model's scope-visibility enumeration so
    /// completion applies the same first-occurrence-wins rule as resolution.
    /// </summary>
    internal static string OpenTargetDedupKey(Expr openExpr, int index)
        => openExpr is Expr.AlgorithmExpr or Expr.Capture
            ? $"(inline#{index})"
            : Evaluator.OpenExprName(openExpr);

    public static IReadOnlyList<PropertyLookupHit> LookupLexicalPropertyMatches(ElaboratedPropertyScope scope, string name)
    {
        if (TryLookupDirectLexicalProperty(scope, name) is { } directHit)
            return [directHit];

        return LookupOpenPropertyMatches(scope, name);
    }

    private static ElaboratedPropertyScope? CreateParentScope(ScopeCtx? parent)
        => parent is null ? null : CreateScope(parent);

    private static ElaboratedPropertyScope CreateScope(ScopeCtx scope)
        => new(
            CreateParentScope(scope.Parent),
            scope.Opens,
            CreatePropertyHits(CreateSyntheticOwner(scope), scope.Properties));

    private static IReadOnlyList<PropertyLookupHit> CreatePropertyHits(Algorithm owner, IReadOnlyList<Property> properties)
    {
        var hits = new List<PropertyLookupHit>(properties.Count);
        foreach (var property in properties)
            hits.Add(new PropertyLookupHit(owner, property));
        return hits;
    }

    private static Algorithm CreateSyntheticOwner(ScopeCtx scope)
        => new Algorithm.User(
            Parent: null,
            Parameters: [],
            Opens: scope.Opens,
            Properties: scope.Properties,
            Output: []);

}
