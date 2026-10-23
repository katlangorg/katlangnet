using System.Collections.Immutable;
using System.Globalization;
using System.Text;

namespace KatLang.ParserFuzz;

/// <summary>
/// Corpus-level accounting (SEM-2B). Definitions:
/// <list type="bullet">
/// <item><b>generated</b> — cases enumerated (nothing evaluated);</item>
/// <item><b>parsed-clean</b> — valid cases whose every member passed the front end with no diagnostic;</item>
/// <item><b>executed</b> — profile runs that reached their surface (members included);</item>
/// <item><b>accepted</b> — cases whose verdict is <see cref="SemanticVerdict.Passed"/>;</item>
/// <item><b>rejected path claims</b> — evidence-backed path claims the required profile did not show
/// (never a pass of that path; the case's semantic anchors still apply);</item>
/// <item><b>mismatching / front-end / harness / timed-out / crashed</b> — the failing verdict classes.</item>
/// </list>
/// Large counts are not coverage: the floors in <see cref="Floors"/> are what make the suite
/// non-vacuous.
/// </summary>
internal sealed class SemanticCoverage
{
    public int Generated { get; private set; }
    public int ValidCases { get; private set; }
    public int InvalidCases { get; private set; }
    public int ParsedClean { get; private set; }
    public int Executed { get; private set; }
    public int Accepted { get; private set; }
    public int PathClaims { get; private set; }

    public SortedDictionary<SemanticVerdict, int> Verdicts { get; } = [];
    public SortedDictionary<string, int> PassedByFamily { get; } = new(StringComparer.Ordinal);
    public SortedDictionary<string, int> PassedByFeature { get; } = new(StringComparer.Ordinal);
    public SortedDictionary<string, int> RunsByProfile { get; } = new(StringComparer.Ordinal);
    public SortedDictionary<string, int> Relations { get; } = new(StringComparer.Ordinal);
    public SortedDictionary<string, int> PathsExercised { get; } = new(StringComparer.Ordinal);
    public SortedDictionary<string, int> RejectionReasons { get; } = new(StringComparer.Ordinal);
    public SortedDictionary<string, int> Kinds { get; } = new(StringComparer.Ordinal);
    public List<(SemanticCase Case, SemanticCaseResult Result)> Passed { get; } = [];

    public int RejectedPathClaims => RejectionReasons.Values.Sum();

    public static SemanticCoverage Of(IEnumerable<(SemanticCase Case, SemanticCaseResult Result)> outcomes)
    {
        var coverage = new SemanticCoverage();
        foreach (var (semanticCase, result) in outcomes) coverage.Add(semanticCase, result);
        return coverage;
    }

    private void Add(SemanticCase semanticCase, SemanticCaseResult result)
    {
        Generated++;
        Bump(Kinds, semanticCase.Kind.ToString());
        if (semanticCase.Kind == SemanticCaseKind.InvalidFrontEnd) InvalidCases++;
        else
        {
            ValidCases++;
            if (!result.Runs.IsEmpty && !result.Findings.Any(f => f.Contains("rejected by the front end", StringComparison.Ordinal))) ParsedClean++;
        }

        Verdicts[result.Verdict] = Verdicts.GetValueOrDefault(result.Verdict) + 1;
        foreach (var run in result.Runs)
        {
            if (run.Ran || run.Cancelled) Executed++;
            if (run.Ran || run.Cancelled) Bump(RunsByProfile, run.Profile);
        }

        PathClaims += BitCount(semanticCase.Paths & SemanticPath.EvidenceBacked);
        foreach (var rejection in result.PathRejections) Bump(RejectionReasons, rejection.Split(':')[0]);
        if (!result.Passed) return;

        Accepted++;
        Passed.Add((semanticCase, result));
        if (semanticCase.Kind != SemanticCaseKind.InvalidFrontEnd)
            foreach (var family in semanticCase.Families) Bump(PassedByFamily, family);
        foreach (var feature in semanticCase.Features.Where(f => semanticCase.Kind != SemanticCaseKind.InvalidFrontEnd || f.StartsWith("invalid-", StringComparison.Ordinal)))
            Bump(PassedByFeature, feature);
        foreach (var relation in result.RelationsChecked) Bump(Relations, relation);
        foreach (var path in Enum.GetValues<SemanticPath>())
        {
            if (path is SemanticPath.None or SemanticPath.EvidenceBacked || BitCount(path) != 1) continue;
            if (result.PathsExercised.HasFlag(path)) Bump(PathsExercised, path.ToString());
        }
    }

    /// <summary>Explicit coverage floors for the fixed CI corpus. Returns every violated floor.</summary>
    public IReadOnlyList<string> Floors(IReadOnlyList<(string A, string B)> requiredInteractions)
    {
        var violations = new List<string>();
        foreach (var family in SemanticGrammar.Families)
        {
            if (PassedByFamily.GetValueOrDefault(family) < 8)
                violations.Add($"family '{family}' has {PassedByFamily.GetValueOrDefault(family)} accepted cases (floor 8)");
        }

        foreach (var (a, b) in requiredInteractions)
        {
            var count = Passed.Count(p => p.Case.Features.Contains(a) && p.Case.Features.Contains(b));
            if (count == 0) violations.Add($"selected interaction ({a} x {b}) has no accepted case");
        }

        foreach (var profile in SemanticProfiles.All)
        {
            if (RunsByProfile.GetValueOrDefault(profile.Id) == 0)
                violations.Add($"profile '{profile.Id}' was never executed");
        }

        foreach (var pair in SemanticProfiles.Pairs)
        {
            if (Relations.GetValueOrDefault(pair.Id) == 0) violations.Add($"declared comparison {pair.Id} never ran");
        }

        foreach (var role in new[] { SemanticMember.AlphaRenameRole, SemanticMember.DeclarationReorderRole })
        {
            if (Relations.GetValueOrDefault("relation:" + role) == 0) violations.Add($"relation {role} never ran");
        }

        foreach (var path in Enum.GetValues<SemanticPath>())
        {
            if (path is SemanticPath.None or SemanticPath.EvidenceBacked || BitCount(path) != 1) continue;
            if (PathsExercised.GetValueOrDefault(path.ToString()) == 0) violations.Add($"intended path {path} has zero exercised cases");
        }

        foreach (var production in SemanticGrammar.InvalidProductions)
        {
            if (PassedByFeature.GetValueOrDefault("invalid-" + production.Name) == 0)
                violations.Add($"invalid production '{production.Name}' has no accepted case");
        }

        foreach (var kind in Enum.GetValues<SemanticCaseKind>())
        {
            if (Passed.Count(p => p.Case.Kind == kind) == 0) violations.Add($"case kind {kind} has no accepted case");
        }

        foreach (var context in SemanticGrammar.Contexts.Skip(1))
        {
            if (PassedByFeature.GetValueOrDefault("ctx-" + context) == 0) violations.Add($"context '{context}' has no accepted case");
        }

        // Widespread rejection must not leave the suite green: at most one claim in ten may be rejected.
        if (RejectedPathClaims * 10 > PathClaims)
            violations.Add($"{RejectedPathClaims} of {PathClaims} evidence-backed path claims were rejected (ceiling 10%)");

        return violations;
    }

    public string Describe()
    {
        var text = new StringBuilder();
        text.AppendLine(string.Create(CultureInfo.InvariantCulture,
            $"generated={Generated} valid={ValidCases} invalid={InvalidCases} parsed-clean={ParsedClean} executed-runs={Executed} accepted={Accepted} path-claims={PathClaims} rejected-path-claims={RejectedPathClaims}"));
        text.AppendLine("verdicts: " + string.Join(", ", Verdicts.Select(p => $"{p.Key}={p.Value}")));
        text.AppendLine("kinds: " + Join(Kinds));
        text.AppendLine("families: " + Join(PassedByFamily));
        text.AppendLine("profiles: " + Join(RunsByProfile));
        text.AppendLine("relations: " + Join(Relations));
        text.AppendLine("paths: " + Join(PathsExercised));
        text.AppendLine("rejections: " + Join(RejectionReasons));
        text.AppendLine("features: " + Join(PassedByFeature));
        return text.ToString();
    }

    private static string Join(SortedDictionary<string, int> map) => string.Join(", ", map.Select(p => $"{p.Key}={p.Value.ToString(CultureInfo.InvariantCulture)}"));

    private static void Bump(SortedDictionary<string, int> map, string key) => map[key] = map.GetValueOrDefault(key) + 1;

    private static int BitCount(SemanticPath path) => System.Numerics.BitOperations.PopCount((uint)path);
}
