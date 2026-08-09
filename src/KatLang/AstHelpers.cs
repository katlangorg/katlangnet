using System.Diagnostics.CodeAnalysis;

namespace KatLang;

internal static class AstHelpers
{
    internal static bool TryGetUnresolvedLoadArguments(
        this Expr expr,
        [NotNullWhen(true)] out OutputBundle? args)
    {
        if (expr is Expr.Call(Expr.Resolve(var name), var loadArgs) && name == "load")
        {
            args = loadArgs;
            return true;
        }

        args = null;
        return false;
    }

    internal static Property WithValue(this Property property, Algorithm value)
        => new(property.Name, value, property.IsPublic, property.Exposure)
        {
            DeclarationSpans = property.DeclarationSpans,
        };

    /// <summary>
    /// Collapses a wrapper algorithm whose single output row is a scope-owning
    /// algorithm expression into that algorithm (module elaboration's
    /// single-block property-body promotion). A <see cref="Expr.Capture"/> body
    /// never collapses — a captured value boundary is not algorithm identity —
    /// the unwrap predicate is the structural node kind.
    /// </summary>
    internal static Algorithm UnwrapSingleBlockPropertyBody(this Algorithm algorithm)
    {
        if (algorithm is Algorithm.User
            {
                Params.Count: 0, Opens.Count: 0, Properties.Count: 0,
                Output: [Expr.AlgorithmExpr(var innerAlgorithm)]
            })
        {
            return innerAlgorithm;
        }

        return algorithm;
    }
}
