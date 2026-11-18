namespace KatLang.Tests;

/// <summary>
/// THE COMPLETED-CONTEXT CONTRACT of exposure (ONE SUMMARY MODE, November 2026; implementation-only, no Lean
/// counterpart): <see cref="CompletedStructureContext.For"/> returns a completed structural context for every body an
/// exposure run descends into — a property value, a block literal, a branch body, a loaded module's root — and for a
/// deferred branch body when its region materializes, so every level is summarized and settled in the context of the
/// scope it is written in. There is no contextless mode to fall back to: a level without a context is an internal error
/// (<c>PropertyExposureResolver.ProcessScopeBody</c>, <c>UnchargedByFamily</c>), never a summary without origins.
///
/// <para>Each case adds bodies of ONE kind to a control program and pins how many exposure levels that adds
/// (<see cref="FrontEndTraversalObservations.ExposureAlgorithmExpansions"/>, one per level descended into), so the bodies
/// are reached rather than skipped, together with the classification their reads require; every source is legal. The
/// deferred branch body is checked where it is elaborated, at the run that selects it.</para>
/// </summary>
public sealed class ExposureCompletedContextTests
{
    private const string Module = "https://katlang.org/exposure-context/m.kat";

    private static RunOptions Options(Action? fetched = null) => new()
    {
        DownloadCode = (url, _) =>
        {
            Assert.Equal(Module, url);
            fetched?.Invoke();
            return ValueTask.FromResult("public X = 3\n");
        },
    };

    private static string Program(string added, string output = "A")
        => $"F(y) = {{\n  A = y + 1\n{added}  {output}\n}}\nF(2)\n";

    private static async Task<(Algorithm Root, long Levels)> Exposed(string source)
    {
        var observations = new FrontEndTraversalObservations();
        var parsed = await Parser.ParseObservedAsync(source, Options(), observations);
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics));
        return (parsed.Root, observations.ExposureAlgorithmExpansions);
    }

    private static Property Member(Algorithm owner, params string[] path)
    {
        var property = Assert.Single(owner.Properties, p => p.Name == path[0]);
        return path.Length == 1 ? property : Member(property.Value, path[1..]);
    }

    // The levels each case adds: B's body; C's value, the block literal it reads and the block's Q; the two branch
    // bodies (a parsed family owns no open, so it is no level of its own); the loaded module's root and its X.
    [Theory]
    [InlineData("property", "  B(z) = z + y\n", "B", 1)]
    [InlineData("block", "  C = { public Q = y }.Q + 0\n", "C", 3)]
    [InlineData("branches", "  G(0) = y\n  G(n) = n + y\n", "G", 2)]
    [InlineData("module", $"  H = load('{Module}')\n", "H", 2)]
    public async Task EveryBodyKind_IsAnExposureLevel_SettledInItsCompletedContext(string kind, string added, string declared, long addedLevels)
    {
        var (_, control) = await Exposed(Program(""));
        var (root, levels) = await Exposed(Program(added));
        Assert.Equal(addedLevels, levels - control);
        var property = Member(root, "F", declared);
        if (kind == "module")
        {
            // A loaded module is rooted at the prelude: nothing it declares can require F's parameter.
            Assert.Equal(PropertyExposure.Exported, property.Exposure);
            Assert.Equal(PropertyExposure.Exported, Member(property.Value, "X").Exposure);
        }
        else
        {
            Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, property.Exposure);
            Assert.Equal([new CapturedParameterRequirement("y", 0)], property.CaptureRequirements);
        }
    }

    /// <summary>
    /// A branch that loads a module is a deferred unit: the parse classifies its family from the provisional body without
    /// fetching, and the run that selects the branch materializes it, deriving the materialized body's completed context
    /// and comparing its contribution with the family's (<c>UnchargedByFamily</c>), then elaborating it. A context the
    /// derivation could not give is an internal error, so the run's result is the evidence; a run that never selects the
    /// branch never fetches.
    /// </summary>
    [Fact]
    public async Task DeferredBranchBody_IsElaboratedInItsCompletedContext_WhenItMaterializes()
    {
        const string Added = $"  K(0) = 0\n  K(n) = {{\n    open '{Module}'\n    X + n + y\n  }}\n";
        var fetches = 0;
        var parsed = await Parser.ParseAsync(Program(Added, output: "K(1)"), Options(() => fetches++));
        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics));
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, Member(parsed.Root, "F", "K").Exposure);
        Assert.Equal(0, fetches);

        foreach (var (output, expected, expectedFetches) in new[] { ("K(0)", "0", 0), ("K(1)", "6", 1) })
        {
            fetches = 0;
            var result = await KatLangEngine.RunAsync(Program(Added, output), Options(() => fetches++));
            Assert.Equal(expected, Assert.IsType<RunResult.Success>(result).ToDisplayString());
            Assert.Equal(expectedFetches, fetches);
        }
    }
}
