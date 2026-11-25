using System.Collections.Immutable;
using KatLang;
using Xunit;

namespace KatLang.Formatting.PublicApi.Tests;

public class RequiredAncestorPublicContractTests
{
    [Fact]
    public void ElaboratedLists_PreservePropertyRecordReferenceEquality()
    {
        var parsed = Parser.Parse("O(x) = {\n A = x\n B = x\n A\n}\n1");
        Assert.Empty(parsed.Diagnostics);
        var root = parsed.Root;
        var owner = Assert.IsType<Algorithm.User>(root.Properties[0].Value);
        var a = owner.Properties[0];
        var b = owner.Properties[1];
        var first = new Property("P", a.Value) { RequiredAncestorParameters = a.RequiredAncestorParameters };
        var second = first with { RequiredAncestorParameters = b.RequiredAncestorParameters };
        Assert.False(first == second);
        Assert.False(first.Equals(second));
        Assert.Equal(2, new HashSet<Property> { first, second }.Count);
        Assert.True(first == (first with { }));
        Assert.Equal(first.GetHashCode(), (first with { }).GetHashCode());
        Assert.NotSame(a.RequiredAncestorParameters, b.RequiredAncestorParameters);
        Assert.Contains("RequiredAncestorParameters = System.String[]", first.ToString());
    }

    [Fact]
    public void LocalOnlyError_TextAndEqualityDependOnContents()
    {
        IReadOnlyList<string>[] lists =
        [new[] { "A", "a10", "a2" }, Array.AsReadOnly(new[] { "A", "a10", "a2" }),
            ImmutableList.Create("A", "a10", "a2"), ImmutableSortedSet.Create(StringComparer.Ordinal, "A", "a10", "a2")];
        var error = new EvalError.LocalOnlyProperty("O", "P", PropertyExposure.LocalOnlyCapturedAncestorParameters)
            { RequiredParameters = lists[0] };
        const string expected = "LocalOnlyProperty { Span = , IsResourceLimit = False, Code = LocalOnlyProperty, ObjectDesc = O, PropertyName = P, Exposure = LocalOnlyCapturedAncestorParameters, RequiredParameters = [A, a10, a2] }";
        foreach (var list in lists)
        {
            var copy = error with { RequiredParameters = list };
            Assert.Equal(expected, copy.ToString());
            Assert.True(error == copy);
            Assert.Equal(error.GetHashCode(), copy.GetHashCode());
        }
        Assert.False(error == (error with { RequiredParameters = new[] { "a2", "a10", "A" } }));
        Assert.False(error == (error with { RequiredParameters = null }));
        Assert.False(error == (error with { PropertyName = "Q" }));
        Assert.Contains("RequiredParameters = []", (error with { RequiredParameters = Array.Empty<string>() }).ToString());
        Assert.Contains("RequiredParameters =  }", (error with { RequiredParameters = null }).ToString());
    }
}
