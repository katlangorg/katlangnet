using System.Text;

namespace KatLang.Tests.LanguageSpec;

/// <summary>
/// Generates and pins <c>lean/LanguageSpecCases.lean</c>: the Lean half of the
/// canonical executable language specification. Unlike the semantic-explorer
/// artifact (which pins C#-observed behavior), every <c>#guard</c> here pins
/// the CANONICAL expectation written in <see cref="LanguageSpecCorpus"/>. The
/// C# runner asserts the C# engine matches the same canonical neutral
/// observation, so a Lean/C# disagreement on any Lean-guarded case is
/// impossible without a failure in one of the two build stages.
///
/// Regenerate with:
///   $env:KATLANG_REGENERATE_LANGUAGE_SPEC = "1"
///   dotnet test .\KatLang.slnx --filter LanguageSpecArtifacts
/// </summary>
public class LanguageSpecArtifactsTests
{
    internal const string RegenerateVariable = "KATLANG_REGENERATE_LANGUAGE_SPEC";
    private const string ArtifactRelativePath = "lean/LanguageSpecCases.lean";

    [Fact]
    public void GeneratedLeanArtifact_MatchesCanonicalCorpus()
    {
        var expected = GenerateArtifact();
        var path = Path.Combine(RepoRoot.Find(), ArtifactRelativePath);

        if (Environment.GetEnvironmentVariable(RegenerateVariable) == "1")
        {
            File.WriteAllText(path, expected);
            return;
        }

        Assert.True(File.Exists(path),
            $"{ArtifactRelativePath} is missing. Set {RegenerateVariable}=1 and rerun this test to generate it.");

        var actual = File.ReadAllText(path).ReplaceLineEndings("\n");
        Assert.True(expected == actual,
            $"{ArtifactRelativePath} is out of date with the canonical corpus. " +
            $"Set {RegenerateVariable}=1, rerun this test, review the diff, and run " +
            "`lake build LanguageSpecCases` to check the Lean side.");
    }

    /// <summary>
    /// The generated artifact contains exactly one observation guard per
    /// Lean-guarded case plus one count guard — enforced against the corpus
    /// partition rather than a handwritten total.
    /// </summary>
    [Fact]
    public void GeneratedArtifact_GuardCountMatchesPartition()
    {
        var leanGuarded = LanguageSpecCorpus.AllCases().Count(c => c.IsLeanRepresentable);
        var artifact = GenerateArtifact();
        var guardLines = artifact.Split('\n').Count(line => line.StartsWith("#guard ", StringComparison.Ordinal));
        Assert.Equal(leanGuarded + 1, guardLines);
    }

    internal static string GenerateArtifact()
    {
        var cases = LanguageSpecCorpus.AllCases();
        var leanGuarded = cases.Where(c => c.IsLeanRepresentable).ToList();
        var parseLevel = cases.Count(c => c.Outcome == SpecOutcome.ParseError);
        var csharpOnly = cases.Count(c => !c.IsLeanRepresentable && c.Outcome != SpecOutcome.ParseError);

        var builder = new StringBuilder();
        builder.Append($"""
            import KatLang

            /-!
            GENERATED FILE - DO NOT EDIT BY HAND.

            Canonical executable language specification, Lean half
            (source corpus: tests/KatLang.Tests/LanguageSpec/LanguageSpecCorpus.cs).

            Each `#guard` pins the CANONICAL expectation of one specification case —
            not an observed value. The C# runner (LanguageSpecRunnerTests) asserts the
            C# engine matches the same canonical neutral observation, so together the
            two builds keep Lean, C#, and the specification aligned case-by-case.
            This is bounded differential validation over the Lean-guarded partition,
            not a formal verification of the evaluators.

            Partition (machine-checked by the `specCaseIds.length` guard below):
            - specification surface cases: {cases.Count}
            - excluded parse-level cases (Lean has no surface parser): {parseLevel}
            - excluded C#-only cases (each carries an explicit reason in the corpus): {csharpOnly}
            - Lean-guarded cases: {leanGuarded.Count}
            - probe observations (C#-only by design): {cases.Sum(c => c.Probes.Count)}
            - internal-node cases live in the semantic-explorer corpus, not here: see
              lean/SemanticExplorerCases.lean

            Regenerate from the repo root with:
              $env:KATLANG_REGENERATE_LANGUAGE_SPEC = "1"
              dotnet test .\KatLang.slnx --filter LanguageSpecArtifacts
            -/

            namespace LanguageSpecCases
            open KatLang

            """.ReplaceLineEndings("\n"));
        builder.Append('\n');
        builder.Append(LeanObsTemplate.SharedDefinitions.ReplaceLineEndings("\n"));
        builder.Append("\n\n");

        var emittedIds = new List<string>();
        foreach (var specCase in leanGuarded)
        {
            var leanName = specCase.Id.Replace('-', '_');
            var sourceComment = specCase.Source.Replace("\n", " \\n ");
            builder.Append($"-- {specCase.Id} [{specCase.Category}]: {sourceComment}\n");
            builder.Append($"def case_{leanName} : Expr :=\n  {specCase.LeanProgram}\n");
            builder.Append($"#guard obs case_{leanName} == \"{specCase.CanonicalNeutral}\"\n\n");
            emittedIds.Add(specCase.Id);
        }

        builder.Append($"-- {emittedIds.Count} canonical Lean-guarded specification cases.\n\n");

        SemanticExplorerLeanArtifactTests.AppendCountGuard(builder, "specCaseIds", emittedIds, leanGuarded.Count,
            "Machine-checked Lean-guarded partition count: the id list is built by the\n" +
            "same loop that emits the guards above, while the expected total is computed\n" +
            "independently from the corpus partition, so a generation bug fails `lake build`.");

        builder.Append("end LanguageSpecCases\n");
        return builder.ToString();
    }
}

/// <summary>Locates the repository root shared by artifact generators.</summary>
internal static class RepoRoot
{
    public static string Find()
    {
        var directory = AppContext.BaseDirectory;
        while (directory is not null && !File.Exists(Path.Combine(directory, "KatLang.slnx")))
            directory = Path.GetDirectoryName(directory);

        return directory
            ?? throw new InvalidOperationException("Could not locate repo root (KatLang.slnx) above test bin directory.");
    }
}
