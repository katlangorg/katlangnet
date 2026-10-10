namespace KatLang.Tests;

/// <summary>
/// Phase A3 (2026-10-10) pin for the one gap the Model-C reconciliation of PAR-07 found: a formula's lifting
/// ROLE is a STATIC classification of the written position, never a run-time demand. A clause family's
/// argument is a VALUE role, so a formula lifts a callable written there that requires supplied arguments —
/// the callee's parameter joins the formula's inferred signature whether or not a run ever selects a clause
/// that reads it — and the synthesized call is then an ordinary supplied computation, which the family
/// demands only when a clause pattern inspects it or a selected body reads it (NEED-01, NEED-04). Observed
/// on the six routes of <c>ModelCProductionTests.Observe</c>, with the exact host-call log.
/// </summary>
public class ModelCA3ReconciliationTests
{
    private const string Definitions = "A = trace(x) + 1\nChoose(0, a) = 0\nChoose(n, a) = a\n";

    private static readonly RunOptions HostVocabulary = new()
    {
        HostOperations = HostOperations.Create(
            HostOperation.Create("tick", static (_, _) => new Result.Atom(0)),
            HostOperation.Create("trace", static (args, _) => args[0], "x")),
    };

    [Theory]
    [InlineData("F = Choose(0, A)\nF(5)", "0", "")]
    [InlineData("F = Choose(0, A)\nF(5), F(6)", "(0, 0)", "")]
    [InlineData("F = Choose(1, A)\nF(5)", "6", "5")]
    [InlineData("F = Choose(1, A) + Choose(0, A)\nF(5)", "6", "5")]
    [InlineData("F = Choose(1, A) + Choose(1, A)\nF(5)", "12", "5,5")]
    public async Task StaticValueRoleLifts_AndOnlyAClauseThatReadsTheArgumentDemandsTheLiftedCall(
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
    [InlineData("F = Choose(0, A)\nF(5)")]
    [InlineData("F = Choose(1, A)\nF(5)")]
    public void TheLiftedParameter_JoinsTheFormulasSignature_WhicheverClauseARunSelects(string program)
    {
        var parsed = Parser.Parse(Definitions + program, HostVocabulary);
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics));
        var formula = Assert.IsType<Algorithm.User>(Assert.Single(parsed.Root.Properties, property => property.Name == "F").Value);
        Assert.Equal(["x"], formula.ParameterPatterns.Select(static pattern => pattern.DisplayName));
    }
}
