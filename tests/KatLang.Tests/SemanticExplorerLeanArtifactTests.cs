using System.Text;

namespace KatLang.Tests;

/// <summary>
/// Generates and pins <c>lean/SemanticExplorerCases.lean</c>: the Lean/C#
/// differential half of the semantic explorer. Every Lean-representable
/// corpus case is emitted as a Lean AST construction plus a <c>#guard</c>
/// pinning the neutral observation the C# evaluator produced. If C# behavior
/// changes, this test fails (regenerate and review the diff); if Lean behavior
/// diverges from the recorded observation, <c>lake build SemanticExplorerCases</c>
/// fails on the guard. Together they keep the two implementations observably
/// aligned on the whole corpus.
///
/// Regenerate with:
///   $env:KATLANG_REGENERATE_SEMANTIC_EXPLORER = "1"
///   dotnet test --filter SemanticExplorerLeanArtifact
/// </summary>
public class SemanticExplorerLeanArtifactTests
{
    private const string RegenerateVariable = "KATLANG_REGENERATE_SEMANTIC_EXPLORER";
    private const string ArtifactRelativePath = "lean/SemanticExplorerCases.lean";

    [Fact]
    public void GeneratedLeanArtifact_MatchesCurrentCSharpObservations()
    {
        var expected = GenerateArtifact();
        var path = Path.Combine(FindRepoRoot(), ArtifactRelativePath);

        if (Environment.GetEnvironmentVariable(RegenerateVariable) == "1")
        {
            File.WriteAllText(path, expected);
            return;
        }

        Assert.True(File.Exists(path),
            $"{ArtifactRelativePath} is missing. Set {RegenerateVariable}=1 and rerun this test to generate it.");

        var actual = File.ReadAllText(path).ReplaceLineEndings("\n");
        Assert.True(expected == actual,
            $"{ArtifactRelativePath} is out of date with current C# evaluator observations. " +
            $"Set {RegenerateVariable}=1, rerun this test, review the diff, and run " +
            "`lake build SemanticExplorerCases` to check the Lean side.");
    }

    /// <summary>
    /// The generated artifact never contains an observation the C# harness
    /// could not classify (exceptions or unintended parse errors on
    /// Lean-representable cases would silently shrink differential coverage).
    /// </summary>
    [Fact]
    public void LeanRepresentableCases_AllProduceComparableObservations()
    {
        foreach (var explorerCase in SemanticExplorerCorpus.AllCases().Where(c => c.LeanProgram is not null))
        {
            var observation = SemanticExplorerHarness.Observe(explorerCase);
            Assert.True(observation.Outcome is "ok" or "err",
                $"{explorerCase.Id} is marked Lean-representable but observed '{observation.Outcome}'.");
        }
    }

    /// <summary>
    /// Pins the corpus partition: the surface corpus splits exactly into
    /// Lean-representable differential cases and C#-parse-level cases (Lean
    /// has no surface parser, so a case is excluded from the artifact iff it
    /// is a deliberate parse-error probe). This keeps the accounting table in
    /// docs/design/sequence-boundary-audit-2026-07.md from drifting: the
    /// artifact guard total is always surfaceCases - parseLevelCases plus the
    /// internal-node cases.
    /// </summary>
    [Fact]
    public void CorpusPartition_LeanExclusionsAreExactlyTheParseLevelCases()
    {
        var allCases = SemanticExplorerCorpus.AllCases();

        foreach (var explorerCase in allCases)
        {
            var isParseError = SemanticExplorerHarness.Observe(explorerCase).Outcome == "parseError";
            Assert.True((explorerCase.LeanProgram is null) == isParseError,
                $"{explorerCase.Id}: LeanProgram is {(explorerCase.LeanProgram is null ? "null" : "set")} " +
                $"but the case {(isParseError ? "is" : "is not")} a parse-error case; " +
                "Lean exclusion and parse-level status must coincide.");
        }

        var excluded = allCases.Where(c => c.LeanProgram is null).Select(c => c.Id)
            .OrderBy(id => id, StringComparer.Ordinal)
            .ToList();
        var expected = SemanticExplorerCorpus.Values.Select(v => $"indexNeg__{v.Id}")
            .Concat(["special__semicolonSeparator", "special__spreadAsBinaryOperand", "special__trailingComma"])
            .OrderBy(id => id, StringComparer.Ordinal)
            .ToList();
        Assert.Equal(expected, excluded);
    }

    internal static string GenerateArtifact()
    {
        var allCases = SemanticExplorerCorpus.AllCases();
        var expectedSurface = allCases.Count(c => c.LeanProgram is not null);
        var expectedInternal = SemanticExplorerCorpus.InternalNodeCases().Count;

        var builder = new StringBuilder();
        builder.Append($"""
            import KatLang

            /-!
            GENERATED FILE - DO NOT EDIT BY HAND.

            Differential corpus for the small-state semantic explorer
            (tests/KatLang.Tests/SemanticExplorerCorpus.cs). Each case is the Lean AST
            construction equivalent to a KatLang source program, and each `#guard` pins
            the neutral observation recorded from the C# evaluator. A failing guard is a
            Lean/C# divergence on that case.

            Partition (machine-checked by the `*CaseIds.length` guards below):
            - surface corpus cases: {allCases.Count}
            - excluded parse-level cases (Lean has no surface parser): {allCases.Count - expectedSurface}
            - Lean-representable surface cases: {expectedSurface}
            - internal-node cases: {expectedInternal}
            - total generated guards: {expectedSurface + expectedInternal} case guards + 2 count guards

            Regenerate from the repo root with:
              $env:KATLANG_REGENERATE_SEMANTIC_EXPLORER = "1"
              dotnet test .\KatLang.slnx --filter SemanticExplorerLeanArtifact
            -/

            namespace SemanticExplorerCases
            open KatLang

            """.ReplaceLineEndings("\n"));
        builder.Append('\n');
        builder.Append(LeanObsTemplate.SharedDefinitions.ReplaceLineEndings("\n"));
        builder.Append("\n\n");

        var surfaceIds = new List<string>();
        foreach (var explorerCase in allCases)
        {
            if (explorerCase.LeanProgram is null)
                continue;

            var observation = SemanticExplorerHarness.Observe(explorerCase);
            if (observation.Outcome is not ("ok" or "err"))
            {
                throw new InvalidOperationException(
                    $"{explorerCase.Id} is Lean-representable but observed '{observation.Outcome}'; refusing to silently shrink the differential corpus.");
            }

            var sourceComment = explorerCase.Source.Replace("\n", " \\n ");
            builder.Append($"-- {explorerCase.Id}: {sourceComment}\n");
            builder.Append($"def case_{explorerCase.Id} : Expr :=\n  {explorerCase.LeanProgram}\n");
            builder.Append($"#guard obs case_{explorerCase.Id} == \"{observation.Neutral}\"\n\n");
            surfaceIds.Add(explorerCase.Id);
        }

        builder.Append($"-- {surfaceIds.Count} differential cases.\n\n");

        AppendCountGuard(builder, "surfaceCaseIds", surfaceIds, expectedSurface,
            "Machine-checked surface partition count: the id list is built by the same\n" +
            "loop that emits the guards above, while the expected total is computed\n" +
            "independently from the corpus partition, so a generation bug fails `lake build`.");

        builder.Append("""
            /-!
            Direct internal-node cases: `Expr.sequenceConstruct` is an INTERNAL node —
            the surface parser never produces it and its value evaluation drops `()`
            leaves, unlike written parentheses. These cases pin that internal behavior
            against the C# evaluator's observations of the same hand-constructed ASTs
            (see tests/KatLang.Tests/SequenceConstructContainmentTests.cs and
            SemanticExplorerCorpus.InternalNodeCases).
            -/

            """.ReplaceLineEndings("\n"));

        var internalIds = new List<string>();
        foreach (var internalCase in SemanticExplorerCorpus.InternalNodeCases())
        {
            var observation = SemanticExplorerHarness.ObserveAst(internalCase.Id, internalCase.RootOutput());
            builder.Append($"-- internal__{internalCase.Id}: {internalCase.Description}\n");
            builder.Append($"def case_internal__{internalCase.Id} : Expr :=\n  .block (alg [] [] [] [{internalCase.LeanRootExpr}])\n");
            builder.Append($"#guard obs case_internal__{internalCase.Id} == \"{observation.Neutral}\"\n\n");
            internalIds.Add($"internal__{internalCase.Id}");
        }

        AppendCountGuard(builder, "internalNodeCaseIds", internalIds, expectedInternal,
            "Machine-checked internal-node partition count (see the surfaceCaseIds note).");

        builder.Append($"-- {internalIds.Count} internal-node cases.\n");
        builder.Append($"-- Total: {surfaceIds.Count + internalIds.Count} case guards ({surfaceIds.Count} surface + {internalIds.Count} internal-node).\n");
        builder.Append("end SemanticExplorerCases\n");
        return builder.ToString();
    }

    /// <summary>
    /// Emits a Lean id-list definition plus a <c>#guard</c> pinning its length
    /// to an independently computed partition count, so the artifact enforces
    /// its own accounting at <c>lake build</c> time instead of via comments.
    /// </summary>
    internal static void AppendCountGuard(
        StringBuilder builder, string listName, IReadOnlyList<string> ids, int expectedCount, string comment)
    {
        builder.Append("/--\n");
        builder.Append(comment);
        builder.Append("\n-/\n");
        builder.Append($"def {listName} : List String := [\n");
        builder.Append(string.Join(",\n", ids.Select(id => $"  \"{id}\"")));
        builder.Append("\n]\n");
        builder.Append($"#guard {listName}.length == {expectedCount}\n\n");
    }

    private static string FindRepoRoot()
    {
        var directory = AppContext.BaseDirectory;
        while (directory is not null && !File.Exists(Path.Combine(directory, "KatLang.slnx")))
            directory = Path.GetDirectoryName(directory);

        return directory
            ?? throw new InvalidOperationException("Could not locate repo root (KatLang.slnx) above test bin directory.");
    }
}
