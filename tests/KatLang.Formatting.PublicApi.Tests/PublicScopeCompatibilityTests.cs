using KatLang;

namespace KatLang.Formatting.PublicApi.Tests;

public class PublicScopeCompatibilityTests
{
    [Fact]
    public void ScopeCtx_ConstructorsShareTheCompleteDeconstructionShape()
    {
        IReadOnlyList<Expr> opens = [];
        IReadOnlyList<Property> properties = [];
        var parameterless = new ScopeCtx(null, opens, properties);
        var (parent, oldOpens, oldProperties, noParameters) = parameterless;
        Assert.Null(parent);
        Assert.Same(opens, oldOpens);
        Assert.Same(properties, oldProperties);
        Assert.Empty(noParameters);

        var current = new ScopeCtx(parameterless, opens, properties, ["n"]);
        var (newParent, newOpens, newProperties, parameters) = current;
        Assert.Same(parameterless, newParent);
        Assert.Same(opens, newOpens);
        Assert.Same(properties, newProperties);
        Assert.Equal(["n"], parameters);
    }
}
