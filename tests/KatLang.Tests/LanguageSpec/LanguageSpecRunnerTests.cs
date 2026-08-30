using System.Text.Json;
using System.Text.RegularExpressions;

namespace KatLang.Tests.LanguageSpec;

/// <summary>
/// Executes every canonical language-spec case through the production front
/// end and evaluator, and validates the corpus schema and partition
/// identities. A failure here means either the implementation drifted from
/// the canonical specification or a canonical case was edited incorrectly —
/// both require review, never regeneration.
/// </summary>
public class LanguageSpecRunnerTests
{
    private static readonly IReadOnlyList<SpecCase> Cases = LanguageSpecCorpus.AllCases();

    private static readonly IReadOnlyDictionary<string, SpecCase> CasesById =
        Cases.ToDictionary(c => c.Id);

    public static TheoryData<string> CaseIds()
    {
        var data = new TheoryData<string>();
        foreach (var specCase in Cases)
            data.Add(specCase.Id);
        return data;
    }

    // ----- Execution ----------------------------------------------------------

    [Theory]
    [MemberData(nameof(CaseIds))]
    public void Case_MatchesCanonicalExpectations(string caseId)
    {
        var specCase = CasesById[caseId];

        if (specCase.Outcome == SpecOutcome.ParseError)
        {
            var parsed = Parser.Parse(specCase.Source);
            Assert.True(parsed.HasErrors, $"{caseId}: expected a parse error, but the source parsed.");

            if (specCase.ExpectedParseDiagnosticFragment is { } fragment)
            {
                Assert.True(
                    parsed.Diagnostics.Any(d => d.Message.Contains(fragment, StringComparison.Ordinal)),
                    $"{caseId}: no parse diagnostic contains \"{fragment}\"; got: "
                    + string.Join(" | ", parsed.Diagnostics.Select(d => d.Message)));
            }

            if (specCase.ExpectedDiagnosticCode is { } expectedCode)
            {
                Assert.True(
                    parsed.Diagnostics.Any(d =>
                        d.Severity == DiagnosticSeverity.Error && d.Code == expectedCode),
                    $"{caseId}: no error diagnostic carries code {expectedCode}; got: "
                    + string.Join(" | ", parsed.Diagnostics.Select(d => $"[{d.Code}] {d.Message}")));
            }

            return;
        }

        var observation = SemanticExplorerHarness.Observe(specCase.Id, specCase.Source);

        if (specCase.Outcome == SpecOutcome.EvalError)
        {
            Assert.True(observation.Outcome == "err",
                $"{caseId}: expected evaluation error ({specCase.ExpectedErrorCategory}), observed {observation.Neutral}.");
            Assert.Equal(specCase.ExpectedErrorCategory, observation.ErrorCategory);
            return;
        }

        Assert.True(observation.Outcome == "ok",
            $"{caseId}: expected successful evaluation, observed {observation.Neutral}.");
        Assert.Equal(specCase.CanonicalNeutral, observation.Neutral);
        Assert.Equal(specCase.ExpectedDisplay, observation.Display!.ReplaceLineEndings("\n"));
    }

    public static TheoryData<string, int> ProbeIds()
    {
        var data = new TheoryData<string, int>();
        foreach (var specCase in Cases)
        {
            for (var i = 0; i < specCase.Probes.Count; i++)
                data.Add(specCase.Id, i);
        }

        return data;
    }

    [Theory]
    [MemberData(nameof(ProbeIds))]
    public void Probe_MatchesCanonicalNeutral(string caseId, int probeIndex)
    {
        var probe = CasesById[caseId].Probes[probeIndex];
        var observation = SemanticExplorerHarness.Observe($"{caseId}@probe{probeIndex}", probe.Probe);
        Assert.Equal(probe.ExpectedNeutral, observation.Neutral);
    }

    // ----- Schema validation --------------------------------------------------

    [Fact]
    public void Schema_IdsAreUniqueKebabCase()
    {
        var idPattern = new Regex("^[a-z0-9]+(-[a-z0-9]+)*$");
        var seen = new HashSet<string>(StringComparer.Ordinal);
        foreach (var specCase in Cases)
        {
            Assert.True(idPattern.IsMatch(specCase.Id), $"'{specCase.Id}' is not kebab-case.");
            Assert.True(seen.Add(specCase.Id), $"Duplicate case id '{specCase.Id}'.");
        }
    }

    [Fact]
    public void Schema_IdsDoNotCollideWithExplorerCorpus()
    {
        var explorerIds = SemanticExplorerCorpus.AllCases().Select(c => c.Id)
            .Concat(SemanticExplorerCorpus.InternalNodeCases().Select(c => $"internal__{c.Id}"))
            .ToHashSet(StringComparer.Ordinal);
        foreach (var specCase in Cases)
        {
            Assert.False(explorerIds.Contains(specCase.Id),
                $"Spec case id '{specCase.Id}' collides with a semantic-explorer case id; the two corpora must stay disjoint authorities.");
        }
    }

    [Fact]
    public void Schema_CategoriesAreDeclared()
    {
        foreach (var specCase in Cases)
        {
            Assert.True(LanguageSpecCorpus.Categories.Contains(specCase.Category),
                $"{specCase.Id}: unknown category '{specCase.Category}'.");
        }
    }

    [Fact]
    public void Schema_ExpectationFieldsMatchOutcome()
    {
        foreach (var specCase in Cases)
        {
            switch (specCase.Outcome)
            {
                case SpecOutcome.Evaluates:
                    Assert.True(specCase.ExpectedDisplay is not null, $"{specCase.Id}: Evaluates requires ExpectedDisplay.");
                    Assert.True(specCase.ExpectedRaw is not null, $"{specCase.Id}: Evaluates requires ExpectedRaw.");
                    Assert.True(specCase.ExpectedEmittedCount is not null, $"{specCase.Id}: Evaluates requires ExpectedEmittedCount.");
                    Assert.True(specCase.ExpectedErrorCategory is null, $"{specCase.Id}: Evaluates forbids ExpectedErrorCategory.");
                    Assert.True(specCase.ExpectedParseDiagnosticFragment is null, $"{specCase.Id}: Evaluates forbids ExpectedParseDiagnosticFragment.");
                    Assert.True(specCase.ExpectedDiagnosticCode is null, $"{specCase.Id}: Evaluates forbids ExpectedDiagnosticCode.");
                    break;
                case SpecOutcome.EvalError:
                    Assert.True(specCase.ExpectedErrorCategory is not null, $"{specCase.Id}: EvalError requires ExpectedErrorCategory.");
                    Assert.True(specCase.ExpectedDisplay is null && specCase.ExpectedRaw is null && specCase.ExpectedEmittedCount is null,
                        $"{specCase.Id}: EvalError forbids value expectations.");
                    Assert.True(specCase.ExpectedParseDiagnosticFragment is null, $"{specCase.Id}: EvalError forbids ExpectedParseDiagnosticFragment.");
                    Assert.True(specCase.ExpectedDiagnosticCode is null, $"{specCase.Id}: EvalError forbids ExpectedDiagnosticCode.");
                    break;
                case SpecOutcome.ParseError:
                    Assert.True(specCase.ExpectedDisplay is null && specCase.ExpectedRaw is null
                        && specCase.ExpectedEmittedCount is null && specCase.ExpectedErrorCategory is null,
                        $"{specCase.Id}: ParseError forbids value/error expectations.");
                    // Every diagnostic-level case pins its structured family, so
                    // new parse-error cases cannot regress to message-only
                    // expectations.
                    Assert.True(specCase.ExpectedDiagnosticCode is not null,
                        $"{specCase.Id}: ParseError requires ExpectedDiagnosticCode.");
                    Assert.True(specCase.ExpectedDiagnosticCode != DiagnosticCode.Unspecified,
                        $"{specCase.Id}: ExpectedDiagnosticCode must be a deliberate non-default family.");
                    Assert.True(specCase.LeanProgram is null,
                        $"{specCase.Id}: parse-error cases are C#-only (Lean has no surface parser).");
                    break;
            }
        }
    }

    [Fact]
    public void Schema_LeanPartitionIsExplicit()
    {
        foreach (var specCase in Cases)
        {
            if (specCase.LeanProgram is not null)
            {
                Assert.True(specCase.LeanExclusionReason is null,
                    $"{specCase.Id}: LeanExclusionReason must be null when LeanProgram is set.");
            }
            else if (specCase.Outcome != SpecOutcome.ParseError)
            {
                Assert.True(specCase.LeanExclusionReason is not null,
                    $"{specCase.Id}: a non-parse-error case without a LeanProgram must state a LeanExclusionReason.");
            }
        }
    }

    [Fact]
    public void Schema_ProbeNeutralsAreWellFormed()
    {
        var neutralPattern = new Regex(@"^(ok raw=.+ n=\d+|err [A-Za-z0-9]+)$");
        foreach (var specCase in Cases)
        {
            var seenProbes = new HashSet<string>(StringComparer.Ordinal);
            foreach (var probe in specCase.Probes)
            {
                Assert.True(seenProbes.Add(probe.Probe), $"{specCase.Id}: duplicate probe program.");
                Assert.True(neutralPattern.IsMatch(probe.ExpectedNeutral),
                    $"{specCase.Id}: probe expectation '{probe.ExpectedNeutral}' is not a neutral observation.");
            }
        }
    }

    // ----- Partition reconciliation --------------------------------------------

    [Fact]
    public void Partition_CountsReconcile()
    {
        var surface = Cases.Count;
        var parseLevel = Cases.Count(c => c.Outcome == SpecOutcome.ParseError);
        var leanGuarded = Cases.Count(c => c.IsLeanRepresentable);
        var csharpOnly = Cases.Count(c => !c.IsLeanRepresentable && c.Outcome != SpecOutcome.ParseError);

        Assert.Equal(surface, parseLevel + leanGuarded + csharpOnly);

        // Parse-level cases are never Lean-guarded (schema also enforces this).
        Assert.Equal(0, Cases.Count(c => c.Outcome == SpecOutcome.ParseError && c.IsLeanRepresentable));

        WriteReport(surface, parseLevel, leanGuarded, csharpOnly);
    }

    private static void WriteReport(int surface, int parseLevel, int leanGuarded, int csharpOnly)
    {
        var report = new
        {
            corpus = "LanguageSpecCorpus",
            // The language-spec partitions. These are DISJOINT from the
            // semantic-explorer corpus partitions (reported separately below);
            // totals from the two corpora must never be blended.
            partition = new
            {
                surfaceCases = surface,
                parseLevelCases = parseLevel,
                leanGuardedCases = leanGuarded,
                csharpOnlyCases = csharpOnly,
                probeObservations = Cases.Sum(c => c.Probes.Count),
                generatorPromptCases = Cases.Count(c => c.IncludeInGeneratorPrompt),
                byCategory = Cases.GroupBy(c => c.Category)
                    .OrderBy(g => g.Key, StringComparer.Ordinal)
                    .ToDictionary(g => g.Key, g => g.Count()),
                csharpOnlyReasons = Cases.Where(c => !c.IsLeanRepresentable && c.Outcome != SpecOutcome.ParseError)
                    .ToDictionary(c => c.Id, c => c.LeanExclusionReason),
            },
            semanticExplorerPartition = new
            {
                surfaceCases = SemanticExplorerCorpus.AllCases().Count,
                leanRepresentable = SemanticExplorerCorpus.AllCases().Count(c => c.LeanProgram is not null),
                internalNodeCases = SemanticExplorerCorpus.InternalNodeCases().Count,
            },
            cases = Cases.Select(c => new
            {
                id = c.Id,
                category = c.Category,
                outcome = c.Outcome.ToString(),
                leanGuarded = c.IsLeanRepresentable,
                canonicalNeutral = c.CanonicalNeutral,
                probes = c.Probes.Count,
                generatorPrompt = c.IncludeInGeneratorPrompt,
            }),
        };

        var path = Path.Combine(AppContext.BaseDirectory, "LanguageSpecReport.json");
        File.WriteAllText(path, JsonSerializer.Serialize(report, new JsonSerializerOptions { WriteIndented = true }));
    }
}
