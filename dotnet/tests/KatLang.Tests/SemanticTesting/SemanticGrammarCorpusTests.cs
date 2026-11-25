using System.Collections.Concurrent;
using System.Text;
using KatLang.ParserFuzz;

namespace KatLang.Tests.SemanticTesting;

/// <summary>
/// SEM-2B: the fixed grammar-aware corpus executed through the shared profile runner. Every case
/// is judged against its CONSTRUCTED expectation (value, emitted count, error kind, exact host
/// events), the declared profile parities, and its well-founded transformations; intended paths
/// are admitted only with execution evidence.
/// </summary>
public class SemanticGrammarCorpusTests
{
    private static readonly Lazy<IReadOnlyList<SemanticCase>> Corpus = new(SemanticCorpus.All);

    private static readonly ConcurrentDictionary<string, SemanticCaseResult> Results = new(StringComparer.Ordinal);

    internal static SemanticCaseResult ResultOf(SemanticCase semanticCase)
        => Results.GetOrAdd(semanticCase.CaseId, _ => SemanticRunner.Run(semanticCase));

    internal static IReadOnlyList<SemanticCase> Cases => Corpus.Value;

    [Fact]
    public void FixedCorpus_EveryCasePassesItsAnchorsParityAndRelations()
    {
        var failures = new List<string>();
        foreach (var semanticCase in Cases)
        {
            var result = ResultOf(semanticCase);
            if (result.Passed) continue;
            failures.Add(Report(semanticCase, result));
        }

        Assert.True(failures.Count == 0,
            $"{failures.Count} of {Cases.Count} SEM-2B cases failed:{Environment.NewLine}{string.Join(Environment.NewLine, failures.Take(12))}");
    }

    /// <summary>
    /// The coverage health check: every family, selected interaction, profile, declared comparison,
    /// transformation, intended path, invalid production, case kind and context must have accepted
    /// cases, and widespread path rejection fails the suite. Zero exercised cases is never green.
    /// </summary>
    [Fact]
    public void FixedCorpus_MeetsEveryCoverageFloor()
    {
        var coverage = SemanticCoverage.Of(Cases.Select(c => (c, ResultOf(c))));
        var violations = coverage.Floors(SemanticCorpus.RequiredInteractions);
        Assert.True(violations.Count == 0,
            "SEM-2B coverage floors violated:" + Environment.NewLine + string.Join(Environment.NewLine, violations)
            + Environment.NewLine + coverage.Describe());
        if (Environment.GetEnvironmentVariable("KATLANG_SEM2B_COVERAGE_OUT") is { Length: > 0 } path)
            File.WriteAllText(path, coverage.Describe());
    }

    internal static string Report(SemanticCase semanticCase, SemanticCaseResult result)
    {
        var text = new StringBuilder();
        text.AppendLine($"== {result.Headline}");
        foreach (var finding in result.Findings.Take(6)) text.AppendLine("   finding: " + finding);
        text.AppendLine("   expected: " + semanticCase.Expected);
        text.AppendLine("   source:");
        foreach (var line in semanticCase.Source.Split('\n')) text.AppendLine("     | " + line);
        foreach (var run in result.Runs.Take(4)) text.AppendLine("   run: " + SemanticRunner.Describe(run));
        return text.ToString();
    }
}
