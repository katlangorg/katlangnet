using KatLang;

namespace KatLang.Formatting.PublicApi.Tests;

public class PublicScopeCompatibilityTests
{
    [Fact]
    public void ScopeCtx_SupportsBothConstructorAndDeconstructionShapes()
    {
        IReadOnlyList<Expr> opens = [];
        IReadOnlyList<Property> properties = [];
        var legacy = new ScopeCtx(null, opens, properties);
        var (parent, oldOpens, oldProperties) = legacy;
        Assert.Null(parent);
        Assert.Same(opens, oldOpens);
        Assert.Same(properties, oldProperties);

        var current = new ScopeCtx(legacy, opens, properties, ["n"]);
        var (newParent, newOpens, newProperties, parameters) = current;
        Assert.Same(legacy, newParent);
        Assert.Same(opens, newOpens);
        Assert.Same(properties, newProperties);
        Assert.Equal(["n"], parameters);
        var (compatibleParent, _, _) = current;
        Assert.Same(legacy, compatibleParent);
    }
}
