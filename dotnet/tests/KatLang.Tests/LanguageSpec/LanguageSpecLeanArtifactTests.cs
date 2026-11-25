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
///   dotnet test .\dotnet\KatLang.slnx --filter LanguageSpecArtifacts
/// That run writes the artifact and then fails by design (see
/// <see cref="ArtifactRegeneration"/>); review the diff, clear the flag, rerun.
/// </summary>
public class LanguageSpecArtifactsTests
{
    private const string ArtifactRelativePath = "lean/LanguageSpecCases.lean";

    [Fact]
    public void GeneratedLeanArtifact_MatchesCanonicalCorpus()
    {
        var expected = GenerateArtifact();
        var path = Path.Combine(RepoRoot.Find(), ArtifactRelativePath);
        var flag = RegenerationFlags.LanguageSpec;

        ArtifactRegeneration.VerifyOrRegenerate(
            flag,
            ArtifactRelativePath,
            regenerate: () => expected,
            verify: () =>
            {
                Assert.True(File.Exists(path),
                    $"{ArtifactRelativePath} is missing. Set {flag}=1 and rerun this test to generate it (that run fails by design).");

                var actual = File.ReadAllText(path).ReplaceLineEndings("\n");
                Assert.True(expected == actual,
                    $"{ArtifactRelativePath} is out of date with the canonical corpus. " +
                    $"Set {flag}=1 and rerun this test to regenerate it (that run fails by design), review the diff, and run " +
                    "`lake build LanguageSpecCases` to check the Lean side. " +
                    SemanticExplorerLeanArtifactTests.DescribeFirstDifference(expected, actual));
            },
            afterRegenerating: "run `lake build LanguageSpecCases` to check the Lean side");
    }

    /// <summary>
    /// Neutral case guards, selected canonical payload guards, independent
    /// projection goldens and the partition guard reconcile with their sources.
    /// </summary>
    [Fact]
    public void GeneratedArtifact_GuardCountMatchesPartition()
    {
        var leanGuarded = LanguageSpecCorpus.AllCases().Count(c => c.IsLeanRepresentable);
        var artifact = GenerateArtifact();
        var guardLines = artifact.Split('\n').Count(line => line.StartsWith("#guard ", StringComparison.Ordinal));
        var payloadGuards = LanguageSpecCorpus.AllCases().Count(c => c.IsLeanRepresentable && c.ExpectedErrorPayload is not null);
        // KL-06 pilot: per pilot case one guard per listed name plus its total guard; the pilot's
        // count guard; and the observation-state guards on `publicationsOf`.
        var pilot = CachePilotCases();
        var cacheGuards = pilot.Sum(c => c.Expectation.Entries.Count + 1) + 1 + LeanObsTemplate.CacheObservationContractGuards;
        Assert.Equal(leanGuarded + payloadGuards + DifferentialErrorContracts.All.Count + 1 + cacheGuards, guardLines);
    }

    /// <summary>
    /// KL-06 pilot on this corpus: the Lean-guarded cases that carry a hand-written
    /// <see cref="SpecCase.ExpectedCachePublications"/>, in corpus order.
    /// </summary>
    internal static IReadOnlyList<CachePilotCase> CachePilotCases()
        => LanguageSpecCorpus.AllCases()
            .Where(c => c.IsLeanRepresentable && c.ExpectedCachePublications is not null)
            .Select(c => new CachePilotCase(c.Id, $"case_{c.Id.Replace('-', '_')}", c.CanonicalNeutral!, c.ExpectedCachePublications!))
            .ToList();

    internal static string GenerateArtifact()
    {
        var cases = LanguageSpecCorpus.AllCases();
        var leanGuarded = cases.Where(c => c.IsLeanRepresentable).ToList();
        var parseLevel = cases.Count(c => c.Outcome == SpecOutcome.ParseError);
        var csharpOnly = cases.Count(c => !c.IsLeanRepresentable && c.Outcome != SpecOutcome.ParseError);
        var cachePilot = CachePilotCases();

        var builder = new StringBuilder();
        builder.Append($"""
            import KatLang

            /-!
            GENERATED FILE - DO NOT EDIT BY HAND.

            Canonical executable language specification, Lean half
            (source corpus: conformance/cases.json).

            Each `#guard` pins the CANONICAL expectation of one specification case —
            not an observed value. The C# runner (LanguageSpecRunnerTests) asserts the
            C# engine matches the same canonical neutral observation, so together the
            two builds keep Lean, C#, and the specification aligned case-by-case.
            This is bounded differential validation over the Lean-guarded partition,
            not a formal verification of the evaluators.

            Partition (machine-checked by the `specCaseIds.length` guard below):
            - specification surface cases: {cases.Count}
            - excluded parse-level cases (Lean has no surface parser): {parseLevel}
            - other shared cases outside the Lean model (each carries an explicit reason in the corpus): {csharpOnly}
            - Lean-guarded cases: {leanGuarded.Count}
            - probe observations (checked by surface runners): {cases.Sum(c => c.Probes.Count)}
            - internal-node cases live in the semantic-explorer corpus, not here: see
              lean/SemanticExplorerCases.lean
            - {CachePilotCase.PartitionLine(cachePilot, leanGuarded.Count)};
              each expectation is HAND-WRITTEN in the corpus (`ExpectedCachePublications`), and the
              C# runner requires the same entries of C#

            Regenerate from the repo root with:
              $env:KATLANG_REGENERATE_LANGUAGE_SPEC = "1"
              dotnet test .\dotnet\KatLang.slnx --filter LanguageSpecArtifacts
            -/

            namespace LanguageSpecCases
            open KatLang

            """.ReplaceLineEndings("\n"));
        builder.Append('\n');
        builder.Append(LeanObsTemplate.SharedDefinitions.ReplaceLineEndings("\n"));
        builder.Append("\n\n");
        LeanObsTemplate.AppendProjectionContracts(builder);
        builder.Append(LeanObsTemplate.CacheObservationDefinitions.ReplaceLineEndings("\n"));
        builder.Append("\n\n");
        LeanObsTemplate.AppendCacheObservationContracts(builder);

        var emittedIds = new List<string>();
        var cachePilotIds = new List<string>();
        foreach (var specCase in leanGuarded)
        {
            var leanName = specCase.Id.Replace('-', '_');
            var sourceComment = specCase.Source.Replace("\n", " \\n ");
            builder.Append($"-- {specCase.Id} [{specCase.Category}]: {sourceComment}\n");
            builder.Append($"def case_{leanName} : Expr :=\n  {specCase.LeanProgram}\n");
            builder.Append($"#guard obs case_{leanName} == {LeanAstEncoder.QuoteString(specCase.CanonicalNeutral ?? "")}\n\n");
            LeanObsTemplate.AppendErrorGuard(builder, $"case_{leanName}", specCase.ExpectedErrorPayload);
            if (specCase.ExpectedCachePublications is { } cacheExpectation)
            {
                // KL-06 pilot: the CANONICAL cache expectation, like every guard of this artifact
                // (LanguageSpecRunnerTests requires the same entries of C#).
                ZeroArgPublicationObserver.AppendCacheGuards(builder, $"case_{leanName}", cacheExpectation);
                cachePilotIds.Add(specCase.Id);
            }

            emittedIds.Add(specCase.Id);
        }

        builder.Append($"-- {emittedIds.Count} canonical Lean-guarded specification cases.\n\n");

        SemanticExplorerLeanArtifactTests.AppendCountGuard(builder, "specCaseIds", emittedIds, leanGuarded.Count,
            "Machine-checked Lean-guarded partition count: the id list is built by the\n" +
            "same loop that emits the guards above, while the expected total is computed\n" +
            "independently from the corpus partition, so a generation bug fails `lake build`.");

        SemanticExplorerLeanArtifactTests.AppendCountGuard(builder, "cachePilotCaseIds", cachePilotIds, cachePilot.Count,
            "Machine-checked KL-06 cache-publication pilot count: one id per case whose cache guards\n" +
            "the loop above emitted; the expected total is the number of Lean-guarded cases that carry\n" +
            "a hand-written cache expectation, computed independently from the corpus.");

        builder.Append("end LanguageSpecCases\n");
        return builder.ToString();
    }
}
