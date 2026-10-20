namespace KatLang.Tests;

public class FailureTerminalityWitnessTests
{
    [Theory]
    [InlineData("trace(1)\n1 / 0\ntrace(3)", "trace(1)")]
    [InlineData("F(x) = trace(x) / (x - 2)\nmap([1, 2, 3], F)", "trace(1),trace(2)")]
    [InlineData("F(x) = trace(x) / (x - 2) > 0\nfilter([1, 2, 3], F)", "trace(1),trace(2)")]
    [InlineData("F(x, acc) = trace(x) / (x - 2) + acc\nreduce([1, 2, 3], F, 0)", "trace(1),trace(2)")]
    [InlineData("Step(n) = if(n == 2, trace(n) / 0, trace(n) + 1)\nrepeat(Step(0), 5)", "trace(0),trace(1),trace(2)")]
    [InlineData("Step(n) = if(n == 2, trace(n) / 0, trace(n) + 1), true\nwhile(Step(0))", "trace(0),trace(1),trace(2)")]
    [InlineData("F(x) = x + x\nF(trace(1) / 0)\ntrace(2)", "trace(1)")]
    public async Task FailureDiscardsOutputAndStopsLaterWork(string source, string expectedCalls)
    {
        var result = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("err", result.Kind);
        Assert.Null(result.Value);
        Assert.Single(result.Errors);
        Assert.StartsWith("DivisionByZero:", result.Errors[0], StringComparison.Ordinal);
        Assert.Equal(expectedCalls.Split(','), result.HostCalls);
    }

    [Theory]
    [InlineData("F(x,y) = x + y\nF(trace(1) / 0, [][trace(2)])", "DivisionByZero:", "trace(1)")]
    [InlineData("F(x,y) = y + x\nF(trace(1) / 0, [][trace(2)])", "BadIndex:", "trace(2)")]
    public async Task FirstExecutedFailureWinsWithoutDemandingTheOtherCell(string source, string code, string calls)
    {
        var result = await SixRouteAgreement.OnEveryRouteAsync(source);
        Assert.Equal("err", result.Kind);
        Assert.Null(result.Value);
        Assert.StartsWith(code, Assert.Single(result.Errors), StringComparison.Ordinal);
        Assert.Equal(new[] { calls }, result.HostCalls);
    }
}
