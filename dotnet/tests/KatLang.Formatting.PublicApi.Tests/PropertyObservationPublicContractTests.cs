namespace KatLang.Formatting.PublicApi.Tests;

/// <summary>
/// The IV-1/IV-2 observation surface as a NuGet consumer meets it (this project is not a friend
/// assembly): a host enables <see cref="RunOptions.ObservePropertyValues"/>, iterates
/// <see cref="RunResult.PropertyObservations"/>, and renders available values — and can neither
/// construct, attach, replace, nor mutate a snapshot or an observation.
/// </summary>
public class PropertyObservationPublicContractTests
{
    [Fact]
    public void Host_EnablesObservation_IteratesAndRendersAvailableValues()
    {
        var result = KatLangEngine.Run(
            "Price = 200\nVAT = Price * 0.21\nTotal = Price + VAT\nUnused = 6 * 7\nTotal",
            new RunOptions { ObservePropertyValues = true });

        var rows = new List<string>();
        foreach (var observation in result.PropertyObservations!)
        {
            rows.Add(observation.Status == PropertyValueStatus.Available
                ? $"{observation.Name} [{observation.DeclarationSpan}] = {result.RenderPropertyValue(observation).Text}"
                : $"{observation.Name} [{observation.DeclarationSpan}] = (withheld)");
        }

        Assert.Equal(["Price [[1:1, 1:6)] = 200", "VAT [[2:1, 2:4)] = 42.00", "Total [[3:1, 3:6)] = 242.00"], rows);
        Assert.Null(KatLangEngine.Run("1").PropertyObservations);
    }

    [Fact]
    public void Consumer_CompilesTheReadPath()
    {
        const string source = """
            using System.Collections.Generic;
            using KatLang;

            public static class Consumer
            {
                public static IReadOnlyList<string> Read(string program)
                {
                    var result = KatLangEngine.Run(program, new RunOptions { ObservePropertyValues = true });
                    var lines = new List<string>();
                    if (result.PropertyObservations is { } observations)
                    {
                        for (var i = 0; i < observations.Count; i++)
                        {
                            PropertyValueObservation o = observations[i];
                            SourceSpan anchor = o.DeclarationSpan;
                            Result? value = o.Value;
                            int rows = o.EmittedCount;
                            lines.Add(o.Status switch
                            {
                                PropertyValueStatus.Available => o.Name + " = " + result.RenderPropertyValue(o).Text + " @" + anchor + " #" + rows + (value is null ? "" : ""),
                                PropertyValueStatus.Withheld => o.Name + " withheld",
                                _ => o.Name,
                            });
                        }
                    }

                    return lines;
                }
            }
            """;

        var compilation = ConsumerCompiler.Compile(source, "observation-reader");
        Assert.True(compilation.ExitCode == 0 && compilation.Diagnostics.Count == 0, compilation.Output);
    }

    [Theory]
    [InlineData("construct-observation", "var o = new PropertyValueObservation();")]
    [InlineData("construct-snapshot", "var s = new PropertyObservations();")]
    [InlineData("attach-snapshot", "var r = KatLangEngine.Run(\"1\"); var c = r with { PropertyObservations = null };")]
    [InlineData("rewrite-observation", "PropertyValueObservation o = null!; var c = o with { Value = null };")]
    [InlineData("mutate-snapshot", "PropertyObservations s = null!; ((ICollection<PropertyValueObservation>)s).Add(null!); s[0] = null!;")]
    public void Consumer_CannotManufactureOrMutateObservations(string probe, string statement)
    {
        var source = $$"""
            using System.Collections.Generic;
            using KatLang;

            public static class Rogue
            {
                public static void Probe()
                {
                    {{statement}}
                }
            }
            """;

        var compilation = ConsumerCompiler.Compile(source, "observation-" + probe);
        Assert.NotEqual(0, compilation.ExitCode);
        Assert.NotEmpty(compilation.Diagnostics);
    }
}
