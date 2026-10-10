namespace KatLang.Tests;

/// <summary>Independent PAR-07/FWD-02 probes: alias target roles apply beyond the second family slot,
/// including inside an unselected builtin branch. Static lifting and runtime demand are independent.</summary>
public class ModelCA3IndependentReviewTests
{
    private const string Definitions = "A = trace(x) + 2\nChoose(0, b, a) = 0\nChoose(n, b, a) = a + a\nC = Choose\nD = C\n";

    private static readonly RunOptions HostVocabulary = new()
    {
        HostOperations = HostOperations.Create(HostOperation.Create("trace", static (args, _) => args[0], "x")),
    };

    [Theory]
    [InlineData("F = D(0, 1 / 0, A)\nF(7)", "0", "")]
    [InlineData("F = D(1, 1 / 0, A)\nF(7)", "18", "7")]
    [InlineData("F = D(1, 1 / 0, A) + D(0, 1 / 0, A)\nF(7)", "18", "7")]
    [InlineData("I = if\nF = I(false, D(1, 1 / 0, A), 12)\nF(7)", "12", "")]
    public async Task ThirdFamilySlotThroughAliases_LiftsStatically_AndIsDemandedOnlyWhenUsed(
        string program, string expected, string effects)
    {
        for (var route = 0; route < 6; route++)
        {
            var observation = await ModelCProductionTests.Observe(Definitions + program, route);
            Assert.True(observation.Error is null, $"route {route}: {observation.Error}");
            Assert.Equal(expected, observation.Value);
            Assert.Equal(effects, observation.Effects);
        }
    }

    [Theory]
    [InlineData("F = D(0, 1 / 0, A)\nF(7)")]
    [InlineData("F = D(1, 1 / 0, A)\nF(7)")]
    [InlineData("F = D(1, 1 / 0, A) + D(0, 1 / 0, A)\nF(7)")]
    [InlineData("I = if\nF = I(false, D(1, 1 / 0, A), 12)\nF(7)")]
    public void ThirdFamilySlotThroughAliases_InfersTheSameBindingInEveryBranch(string program)
    {
        var parsed = Parser.Parse(Definitions + program, HostVocabulary);
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics));
        var formula = Assert.IsType<Algorithm.User>(Assert.Single(parsed.Root.Properties, property => property.Name == "F").Value);
        Assert.Equal(["x"], formula.ParameterPatterns.Select(static pattern => pattern.DisplayName));
    }
}
