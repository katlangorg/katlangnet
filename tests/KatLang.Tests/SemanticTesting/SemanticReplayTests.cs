using KatLang.ParserFuzz;
using System.Text.Json.Nodes;

namespace KatLang.Tests.SemanticTesting;

/// <summary>
/// SEM-2B descriptors and direct replay: versioned round trips, replay through the production
/// pipeline in recipe and exact-source modes, the checked-in v1 fixtures, clear refusal of unknown
/// or malformed descriptors, explicit drift detection, and "nothing verified" never passing.
/// </summary>
public class SemanticReplayTests
{
    private static string FixtureDirectory => Path.Combine(RepoRoot.Find(), "fuzz", "KatLang.ParserFuzz", "SemanticTestcases");

    private static SemanticCase Sample(Func<SemanticCase, bool> predicate)
        => SemanticGrammarCorpusTests.Cases.First(predicate);

    private static SemanticCase Success => Sample(c => c.Kind == SemanticCaseKind.ValidSuccess && c.Tier == "seeded" && c.Members.Length == 3);

    [Fact]
    public void EveryDescriptor_RoundTripsExactly()
    {
        foreach (var semanticCase in SemanticGrammarCorpusTests.Cases)
        {
            var text = SemanticDescriptor.Write(semanticCase);
            Assert.True(SemanticDescriptor.TryParse(text, out var parsed, out var problem), $"{semanticCase.CaseId}: {problem}");
            Assert.Equal(SemanticRecipe.GeneratorId, parsed.Generator);
            Assert.Equal(SemanticRecipe.RecipeVersion, parsed.RecipeVersion);
            Assert.Equal(text, SemanticDescriptor.Write(parsed.Case));
            Assert.Null(SemanticReplay.Drift(parsed.Case, semanticCase));
        }
    }

    [Fact]
    public void Replay_RunsTheProductionPipeline_InBothModes()
    {
        foreach (var semanticCase in new[]
        {
            Success,
            Sample(c => c.Kind == SemanticCaseKind.ValidRuntimeFailure),
            Sample(c => c.Kind == SemanticCaseKind.InvalidFrontEnd),
            Sample(c => c.Paths.HasFlag(SemanticPath.Cancellation)),
        })
        {
            var text = SemanticDescriptor.Write(semanticCase, SemanticRunner.Run(semanticCase));
            var recipe = SemanticReplay.Replay(text, SemanticReplay.Mode.Recipe);
            Assert.True(recipe.Passed, recipe.Report);
            Assert.StartsWith("[recipe]", recipe.Report, StringComparison.Ordinal);
            var exact = SemanticReplay.Replay(text, SemanticReplay.Mode.ExactSource);
            Assert.True(exact.Passed, exact.Report);
            Assert.Contains("recipe not re-verified", exact.Report, StringComparison.Ordinal);
            // Every selected profile ran the base member; every transformation ran once more.
            Assert.Equal(semanticCase.Profiles.Length + semanticCase.Members.Length - 1, recipe.Result!.Runs.Length);
        }
    }

    /// <summary>The checked-in v1 descriptors still rebuild from their recipe and still pass.</summary>
    [Fact]
    public void CheckedInFixtures_ReplayWithoutDrift()
    {
        var files = Directory.GetFiles(FixtureDirectory, "*.json");
        Assert.True(files.Length >= 3, $"expected the checked-in SEM-2B fixtures in {FixtureDirectory}");
        foreach (var file in files)
        {
            var text = File.ReadAllText(file);
            Assert.True(SemanticDescriptor.TryParse(text, out var parsed, out var problem), $"{file}: {problem}");
            Assert.Equal("Passed", parsed.RecordedVerdict);
            var recipe = SemanticReplay.Replay(text, SemanticReplay.Mode.Recipe);
            Assert.True(recipe.Passed, $"{Path.GetFileName(file)}: {recipe.Report}");
            var exact = SemanticReplay.Replay(text, SemanticReplay.Mode.ExactSource);
            Assert.True(exact.Passed, $"{Path.GetFileName(file)}: {exact.Report}");
        }
    }

    [Theory]
    [InlineData("\"format\": \"kl-sem2b-case\"", "\"format\": \"kl-other\"", "unknown descriptor format")]
    [InlineData("\"formatVersion\": 1", "\"formatVersion\": 2", "unsupported kl-sem2b-case version 2")]
    [InlineData("\"generator\": \"sem2b-grammar\"", "\"generator\": \"someone-else\"", "unknown generator")]
    [InlineData("\"kind\": \"valid-success\",\n  \"families\"", "\"kind\": \"valid-sideways\",\n  \"families\"", "unknown case kind")]
    [InlineData("\"id\": \"sync-generic\"", "\"id\": \"sync-imaginary\"", "unknown profile")]
    [InlineData("\"paths\": \"", "\"paths\": \"Teleport, ", "unknown path set")]
    [InlineData("\"value\": \"kl-struct-v1:", "\"value\": \"kl-struct-v9:", "not a valid kl-struct-v1 identity")]
    public void MalformedOrUnknownDescriptors_AreRefusedClearly(string find, string replace, string expectedProblem)
    {
        var text = SemanticDescriptor.Write(Success);
        Assert.Contains(find, text, StringComparison.Ordinal);
        var mutated = ReplaceFirst(text, find, replace);
        Assert.False(SemanticDescriptor.TryParse(mutated, out _, out var problem));
        Assert.Contains(expectedProblem, problem, StringComparison.Ordinal);

        var outcome = SemanticReplay.Replay(mutated, SemanticReplay.Mode.Recipe);
        Assert.False(outcome.Passed);
        Assert.NotNull(outcome.Problem);
    }

    [Fact]
    public void StructurallyBrokenOrOversizedDescriptors_AreRefused()
    {
        Assert.False(SemanticDescriptor.TryParse("{ \"format\": ", out _, out var json));
        Assert.Contains("malformed descriptor JSON", json, StringComparison.Ordinal);
        Assert.False(SemanticDescriptor.TryParse(new string(' ', SemanticDescriptor.MaxDescriptorChars + 1), out _, out var size));
        Assert.Contains("exceeds", size, StringComparison.Ordinal);
        Assert.False(SemanticDescriptor.TryParse("[1, 2]", out _, out var shape));
        Assert.Contains("not a JSON object", shape, StringComparison.Ordinal);

        // A success expectation without its value is a corrupt descriptor, not a vacuous case.
        var text = SemanticDescriptor.Write(Success);
        var start = text.IndexOf("\"value\": \"", StringComparison.Ordinal);
        var end = text.IndexOf('"', start + 10);
        Assert.False(SemanticDescriptor.TryParse(text[..start] + "\"value\": null" + text[(end + 1)..], out _, out var vacuous));
        Assert.Contains("needs a value", vacuous, StringComparison.Ordinal);

        // A tampered source no longer matches its recorded integrity fingerprint.
        var tampered = ReplaceFirst(text, "\\n997\"", "\\n998\"");
        Assert.False(SemanticDescriptor.TryParse(tampered, out _, out var integrity));
        Assert.Contains("does not match its recorded fingerprint", integrity, StringComparison.Ordinal);
    }

    /// <summary>
    /// A recorded source or expectation the recipe no longer produces is DRIFT, reported field by
    /// field; exact-source replay runs what was recorded instead and says that the recipe was not
    /// re-verified.
    /// </summary>
    [Fact]
    public void SourceOrExpectationDrift_IsDetected_NotSilentlyAccepted()
    {
        var semanticCase = Success;
        var altered = semanticCase with
        {
            Members = [new SemanticMember(SemanticMember.BaseRole, semanticCase.Source.Replace("\n997", "\n998", StringComparison.Ordinal)), .. semanticCase.Members.Skip(1)],
        };
        var text = SemanticDescriptor.Write(altered);
        var recipe = SemanticReplay.Replay(text, SemanticReplay.Mode.Recipe);
        Assert.Equal(SemanticVerdict.RecipeDrift, recipe.Verdict);
        Assert.Contains("member 'base' source", recipe.Report, StringComparison.Ordinal);

        // Exact-source runs the recorded (altered) source against the recorded expectation: 998 is
        // not the constructed root control row, so it is a semantic mismatch, not a pass.
        var exact = SemanticReplay.Replay(text, SemanticReplay.Mode.ExactSource);
        Assert.Equal(SemanticVerdict.Mismatch, exact.Verdict);

        var events = semanticCase with { Expected = semanticCase.Expected with { Events = [.. semanticCase.Expected.Events, "trace:77"] } };
        var eventDrift = SemanticReplay.Replay(SemanticDescriptor.Write(events), SemanticReplay.Mode.Recipe);
        Assert.Equal(SemanticVerdict.RecipeDrift, eventDrift.Verdict);
        Assert.Contains("expected events changed", eventDrift.Report, StringComparison.Ordinal);

        var future = ReplaceFirst(SemanticDescriptor.Write(semanticCase), "\"recipeVersion\": 1", "\"recipeVersion\": 2");
        var futureRecipe = SemanticReplay.Replay(future, SemanticReplay.Mode.Recipe);
        Assert.Equal(SemanticVerdict.RecipeDrift, futureRecipe.Verdict);
        Assert.Contains("recipe version 2 is not built", futureRecipe.Report, StringComparison.Ordinal);
        Assert.True(SemanticReplay.Replay(future, SemanticReplay.Mode.ExactSource).Passed);
    }

    [Fact]
    public void SelectingNothing_IsNeverASuccessfulReplayOrCampaign()
    {
        var empty = Directory.CreateTempSubdirectory("katlang-sem2b-empty-");
        try
        {
            Assert.Equal(2, SemanticReplay.RunReplay(["semantic-replay", empty.FullName]));
            Assert.Equal(2, SemanticReplay.RunCorpus(["semantic-corpus", "--only", "sem2b/v1/no-such-prefix", "--out", empty.FullName]));
        }
        finally
        {
            empty.Delete(recursive: true);
        }
    }

    [Fact]
    public void EmptyOrDuplicateProfiles_AndRecordedContractDrift_AreRefusedInBothModes()
    {
        var mutations = new Action<JsonObject>[]
        {
            root => root["profiles"] = new JsonArray(),
            root => root["profiles"]!.AsArray().Add(root["profiles"]![0]!.DeepClone()),
            root => root["members"]!.AsArray().Add(root["members"]![0]!.DeepClone()),
            root => root["profiles"]![0]!["surface"] = "engine-run",
            root => root["profiles"]![0]!["facets"] = "Outcome",
            root => root["profiles"]![0]!["detail"] = "optimizer=off limits=changed",
            root => root["hostFixture"] = "different-host/2",
            root => root["runtimeRandomSeed"] = 17,
            root => root["comparison"]!["errors"] = "ignore-errors",
            root => root["comparison"]!["relations"] = new JsonArray(),
            root => root["expected"]!["paths"] = "128",
            root => root["seed"] = "0x" + new string('F', 1000),
        };
        foreach (var mutate in mutations)
        {
            var root = JsonNode.Parse(SemanticDescriptor.Write(Success))!.AsObject();
            mutate(root);
            foreach (var mode in Enum.GetValues<SemanticReplay.Mode>())
            {
                var result = SemanticReplay.Replay(root.ToJsonString(), mode);
                Assert.False(result.Passed);
                Assert.NotNull(result.Problem);
            }
        }

        var identity = Success with { Seed = Success.Seed + 1, Index = Success.Index + 1 };
        Assert.Contains("generation identity", SemanticReplay.Drift(identity, Success)!, StringComparison.Ordinal);
    }

    /// <summary>The worker writes a result document for every verdict through the same pipeline.</summary>
    [Fact]
    public void Worker_WritesAParsableResult_ThroughTheOrdinaryPipeline()
    {
        var directory = Directory.CreateTempSubdirectory("katlang-sem2b-worker-");
        try
        {
            var semanticCase = Success;
            var descriptor = Path.Combine(directory.FullName, "case.json");
            var result = Path.Combine(directory.FullName, "case.result.json");
            File.WriteAllText(descriptor, SemanticDescriptor.Write(semanticCase));
            Assert.Equal(0, SemanticReplay.Work(descriptor, result, SemanticReplay.Mode.Recipe));
            Assert.True(SemanticDescriptor.TryParseResult(File.ReadAllText(result), out var summary, out var problem), problem);
            Assert.Equal(SemanticVerdict.Passed, summary.Verdict);
            Assert.Equal(semanticCase.CaseId, summary.CaseId);
            foreach (var profile in semanticCase.Profiles)
                Assert.Contains(profile + "/" + SemanticMember.BaseRole, summary.ObservedProfiles);

            Assert.False(SemanticDescriptor.TryParseResult("{\"format\":\"kl-sem2b-result\",\"formatVersion\":1}", out _, out var missing));
            Assert.Contains("malformed result", missing, StringComparison.Ordinal);
        }
        finally
        {
            directory.Delete(recursive: true);
        }
    }

    private static string ReplaceFirst(string text, string find, string replace)
    {
        var at = text.IndexOf(find, StringComparison.Ordinal);
        Assert.True(at >= 0, $"'{find}' not found");
        return text[..at] + replace + text[(at + find.Length)..];
    }
}
