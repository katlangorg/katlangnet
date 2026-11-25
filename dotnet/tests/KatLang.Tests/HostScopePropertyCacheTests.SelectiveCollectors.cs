namespace KatLang.Tests;

public partial class HostScopePropertyCacheTests
{
    [Theory]
    [InlineData("same object", "((2, 1, [1]), (2, 1, [1]))", "tock1")]
    [InlineData("shared properties list", "((2, 1, [1]), (2, 2, [2]))", "tock1,tock2")]
    [InlineData("record with-copy", "((2, 1, [1]), (2, 2, [2]))", "tock1,tock2")]
    public async Task SelectiveCollectorReads_UnderHostScopes_KeepTheirDeclaringOwners(
        string shape, string expected, string effects)
    {
        // Parse the reference and collector as source, then put the same declaration below each
        // host parent. V is a host-owned cached property; the unused second element must stay dormant.
        var function = SourceProvenance.ParseValid("F(*xs) = {\nA = xs\nA.count, A[0], A.take(1)\n}\n0")
            .Root.Properties.Single();
        var outcome = await OnEveryRouteAsync(pre =>
        {
            var (first, second) = HostPair(shape, pre, () => [function, Prop("V", Body(Tick()))]);
            var failure = new Expr.Binary(BinaryOp.Div, N(1), N(0));
            var row = Call("F", R("V"), failure);
            return OpenedTwo(first, row, second, row, sequence: true);
        });

        Assert.Equal((expected, effects), (outcome.Value, outcome.Effects));
    }
}
