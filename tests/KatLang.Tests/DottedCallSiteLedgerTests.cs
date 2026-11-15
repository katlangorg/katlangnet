namespace KatLang.Tests;

/// <summary>
/// The static ledger's charges for formulas that lift STRUCTURAL DOTTED references (<c>Lib.Inc</c>), at increasing
/// numbers of call sites. Resolving such a reference statically meters work and storage: the structural member query
/// registers the written path it reads (<c>StaticStructureOperation.WrittenExpression</c>, charged through
/// <c>StaticQueryResourceBudget.Metadata</c>). Implicit-argument resolution reads an open body's lifted dependencies from
/// its selected composition instead of walking its rows a second time, so the second walk's charges are gone; what
/// remains is the analysis's and the rewrite's own resolution of every site. This pins that every site is still
/// charged (the counters rise with the sites) and that the charges stay linear in them (each doubling of the sites at
/// most about doubles every counter, as <see cref="ReceiverExpansionCostTests"/> bounds receiver expansion). No
/// absolute charge is pinned: what one site costs depends on the shape around it.
/// </summary>
public sealed class DottedCallSiteLedgerTests
{
    private const double LinearGrowth = 2.3;

    private const string Lib = "Lib = {\n    public Inc(x) = x + 1\n    public Twice(y) = y * 2\n}\n";

    /// <summary>One formula per site pair: <c>K{i} = Lib.Inc + Lib.Twice + i</c>.</summary>
    private static string Formulas(int sites)
        => Lib + string.Concat(Enumerable.Range(1, sites / 2).Select(static i => $"K{i} = Lib.Inc + Lib.Twice + {i}\n")) + "0\n";

    /// <summary>One formula with every site: <c>K = Lib.Inc + Lib.Twice + Lib.Inc + …</c>.</summary>
    private static string OneFormula(int sites)
        => Lib + "K = " + string.Join(" + ", Enumerable.Range(1, sites).Select(static i => i % 2 == 0 ? "Lib.Twice" : "Lib.Inc")) + "\n0\n";

    /// <summary>Argument-bearing structural edges exercise the fresh argumentless views in DotEdgeCallee.</summary>
    private static string Calls(int sites)
        => Lib + "K = " + string.Join(" + ", Enumerable.Range(1, sites).Select(static i => $"Lib.Inc({i})")) + "\n0\n";

    [Theory]
    [InlineData("formulas")]
    [InlineData("one-formula")]
    [InlineData("calls")]
    public void EveryDottedSiteIsCharged_AndTheChargesStayLinearInTheSites(string family)
    {
        Func<int, string> source = family switch { "formulas" => Formulas, "calls" => Calls, _ => OneFormula };
        var costs = new[] { 16, 32, 64 }.Select(sites => ReceiverExpansionCostTests.Measure(source(sites))).ToArray();
        for (var i = 1; i < costs.Length; i++)
        {
            var (before, after) = (costs[i - 1], costs[i]);
            Assert.True(after.Adapter > before.Adapter && after.PeakStorage > before.PeakStorage,
                $"{family}: more sites charged no more\n{string.Join("\n", costs.AsEnumerable())}");
            foreach (var ((name, was), (_, now)) in before.Counters().Zip(after.Counters()))
                Assert.True(now <= LinearGrowth * Math.Max(was, 64),
                    $"{family}: {name} grew from {was} to {now} when the sites doubled\n{string.Join("\n", costs.AsEnumerable())}");
        }
    }

    [Fact]
    public void TheFormulasStillLiftEveryDottedSite()
    {
        var program = Formulas(8).Replace("\n0\n", "\nK4(1, 2)\n", StringComparison.Ordinal);
        var root = SourceProvenance.ParseValid(program).Root;
        foreach (var name in new[] { "K1", "K4" })
        {
            var body = Assert.IsType<Algorithm.User>(Assert.Single(root.Properties, property => property.Name == name).Value);
            Assert.Equal("x, y", string.Join(", ", body.ParameterPatterns.Select(static pattern => pattern.DisplayName)));
        }

        Assert.Equal("10", Assert.IsType<RunResult.Success>(KatLangEngine.Run(program)).ToDisplayString());
    }
}
