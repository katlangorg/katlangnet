using static KatLang.Tests.SixRouteAgreement;

namespace KatLang.Tests;

public class DeconstructionExplicitCallDecisionTests
{
    [Theory]
    [InlineData("a, b = 10, 20\na, a(), b(), a(), b", "S[10, 10, 20, 10, 20]", "")]
    [InlineData("p, q = tick(), 5\nx = tick()\np, p(), p(), q(), x, x(), x()",
        "S[1, 1, 1, 5, 2, 3, 4]", "tick#1 | tick#2 | tick#3 | tick#4")]
    [InlineData("p, q = trace(tick()), trace(5)\nq(), p(), q, p, p()",
        "S[5, 1, 5, 1, 1]", "tick#1 | trace(1) | trace(5)")]
    [InlineData("a, b = [tick(), 2]\na(), b(), a, b()",
        "S[1, 2, 1, 2]", "tick#1")]
    [InlineData("F(x) = {a, b = tick() + x, 5\na(), a(), b(), a}\nF(10), F(20)",
        "S[S[11, 11, 5, 11], S[22, 22, 5, 22]]", "tick#1 | tick#2")]
    [InlineData("a, b = tick(), 5\nIgnore(x) = 0\nIgnore(a), Ignore(b), 42", "S[0, 0, 42]", "")]
    [InlineData("a, b = tick(), 5\nStep(x) = x + a()\nrepeat(Step, 3, 0), a()", "S[3, 1]", "tick#1")]
    public async Task ExplicitTargetCalls_ReselectTheSharedSourceAcrossSixRoutes(
        string source, string expected, string effects)
    {
        var observation = await OnEveryRouteAsync(source);
        Assert.True(observation.Kind == "ok", observation.ToString());
        Assert.Equal("ok", observation.Kind);
        Assert.Equal(expected, observation.Value);
        Assert.Empty(observation.Errors);
        Assert.Equal(effects, string.Join(" | ", observation.HostCalls));
    }

    [Fact]
    public async Task ExplicitTargetCalls_ConsumeTheSourceDrawsOnlyOnceAndPreserveTheNextDraw()
    {
        const string source = "a, b = randomInt(1, 1000000), randomInt(1, 1000000)\n"
            + "a(), b(), a, b(), a(), randomInt(1, 1000000)";
        var observation = await OnEveryRouteAsync(source, randomSeed: 7);
        Assert.Equal("ok", observation.Kind);
        Assert.Equal("S[571978, 872323, 571978, 872323, 571978, 78011]", observation.Value);
        Assert.Empty(observation.Errors);
        Assert.Empty(observation.HostCalls);
    }
}
