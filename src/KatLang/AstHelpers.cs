using System.Diagnostics.CodeAnalysis;

namespace KatLang;

internal static class AstHelpers
{
    internal static bool TryGetUnresolvedLoadArguments(
        this Expr expr,
        [NotNullWhen(true)] out Algorithm? args)
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

    internal static bool ShouldUnwrapSingleBlockPropertyBody(this Algorithm innerAlgorithm)
        => innerAlgorithm.IsParametrized
            || innerAlgorithm.Properties.Count > 0
            || innerAlgorithm.Opens.Count > 0;

    internal static Algorithm UnwrapSingleBlockPropertyBody(this Algorithm algorithm)
    {
        if (algorithm is Algorithm.User
            {
                Params.Count: 0, Opens.Count: 0, Properties.Count: 0,
                Output: [Expr.Block(var innerAlgorithm)]
            }
            && innerAlgorithm.ShouldUnwrapSingleBlockPropertyBody())
        {
            return innerAlgorithm with
            {
                IsParametrized = algorithm.IsParametrized || innerAlgorithm.IsParametrized,
            };
        }

        return algorithm;
    }
}
