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

            case Expr.DotCall(var target, var name, null):
            {
                if (name == "Output")
                    return null;

                var targetAlgorithm = ResolveOpenTarget(scope, target);
                return targetAlgorithm is null
                    ? null
                    : TryLookupPublicExportedProperty(targetAlgorithm, name)?.Property.Value;
            }

            case Expr.Combine(var left, var right):
            {
                var leftAlgorithm = ResolveOpenTarget(scope, left);
                var rightAlgorithm = ResolveOpenTarget(scope, right);
                return leftAlgorithm is not null && rightAlgorithm is not null
                    ? CombineAlgorithms(leftAlgorithm, rightAlgorithm)
                    : null;
            }

            case Expr.Block(var algorithm):
                return algorithm;

            default:
                return null;
        }
    }

    public static IReadOnlyList<PropertyLookupHit> LookupOpenPropertyMatches(ElaboratedPropertyScope scope, string name)
    {
        for (var current = scope; current is not null; current = current.Parent)
        {
            List<PropertyLookupHit>? hits = null;

            foreach (var openExpr in current.Opens)
            {
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
            Params: [],
            Opens: scope.Opens,
            Properties: scope.Properties,
            Output: []);

    private static Algorithm CombineAlgorithms(Algorithm left, Algorithm right)
        => new Algorithm.User(
            Parent: null,
            Params: left.Params.Concat(right.Params).ToList(),
            Opens: left.Opens.Concat(right.Opens).ToList(),
            Properties: left.Properties.Concat(right.Properties).ToList(),
            Output: [new Expr.Block(left), new Expr.Block(right)]);
}