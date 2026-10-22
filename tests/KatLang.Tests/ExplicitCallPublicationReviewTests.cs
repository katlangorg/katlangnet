namespace KatLang.Tests;

public class ExplicitCallPublicationReviewTests
{
    [Theory]
    [InlineData("Capture(meta c) = c\nId(x) = x\nId(tick()), tick", "S[1, 2]", 2)]
    [InlineData("Capture(meta c) = c\nR = Capture(tick())\nR.Invoke(), tick", "S[1, 2]", 2)]
    [InlineData("Capture(meta c) = c\nCall0(f) = f()\nR = Capture(tick())\nCall0(R.Algorithm), tick", "S[1, 2]", 2)]
    public async Task NativeOperationInvocation_DoesNotPublish_ThroughRetainedPlans(string source, string expected, int ticks)
    {
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("ok", outcome.Kind);
        Assert.Equal(expected, outcome.Value);
        Assert.Equal(Enumerable.Range(1, ticks).Select(i => $"tick#{i}"), outcome.HostCalls);
    }

    [Theory]
    [InlineData("Call0(R.Algorithm), A", "S[1, 1]", 1)]
    [InlineData("Forward(R.Algorithm), A", "S[1, 1]", 1)]
    [InlineData("Call0(R.Algorithm), Call0(R.Algorithm), A", "S[1, 2, 1]", 2)]
    public async Task SuppliedAlgorithmLink_PreservesTheCapturedBinding(string rows, string expected, int ticks)
    {
        var source = "Capture(meta c) = c\nA = tick()\nR = Capture(A())\nCall0(f) = f()\nForward(g) = Call0(g)\n" + rows;
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("ok", outcome.Kind);
        Assert.Equal(expected, outcome.Value);
        Assert.Equal(Enumerable.Range(1, ticks).Select(i => $"tick#{i}"), outcome.HostCalls);
    }

    [Fact]
    public async Task NestedAlgorithmLinks_PreserveTheUltimateBinding()
    {
        const string source = "Capture(meta c) = c\nA = tick()\nR = Capture(A())\nS = Capture(R.Algorithm())\nCall0(f) = f()\nCall0(S.Algorithm), A";
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("ok", outcome.Kind);
        Assert.Equal("S[1, 1]", outcome.Value);
        Assert.Equal(["tick#1"], outcome.HostCalls);
    }

    [Fact]
    public async Task ADeclaredAlgorithmMember_PublishesItsOwnBinding()
    {
        const string source = "Box = { public Algorithm = tick() }\nCall0(f) = f()\nCall0(Box.Algorithm), Box.Algorithm";
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("ok", outcome.Kind);
        Assert.Equal("S[1, 1]", outcome.Value);
        Assert.Equal(["tick#1"], outcome.HostCalls);
    }

    [Fact]
    public async Task AForwardedLocalBinding_KeepsItsOwningActivation()
    {
        const string source = "Call0(f) = f()\nF(x) = {\n L = x * 100 + tick()\n Call0(L), L\n}\nF(1), F(2), F(1)";
        var outcome = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("ok", outcome.Kind);
        Assert.Equal("S[S[101, 101], S[202, 202], S[103, 103]]", outcome.Value);
        Assert.Equal(["tick#1", "tick#2", "tick#3"], outcome.HostCalls);
    }
}
