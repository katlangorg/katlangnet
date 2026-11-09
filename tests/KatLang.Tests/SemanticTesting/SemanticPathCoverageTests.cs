using System.Globalization;
using System.Text;
using KatLang.ParserFuzz;

namespace KatLang.Tests.SemanticTesting;

/// <summary>
/// SEM-2C: the named <c>sys/path/…</c> block that widens the thin optimizer loop paths
/// (<see cref="SemanticPath.LoopShortCircuit"/>, <see cref="SemanticPath.LoopFallback"/>,
/// <see cref="SemanticPath.GenericInsideOptimizedLoop"/>). The block adds new ids only: every
/// pre-existing case keeps its exact sources, expectation, paths and profiles (pinned by a digest
/// computed before the block was added), and every claim a path case makes is admitted on evidence.
/// </summary>
public class SemanticPathCoverageTests
{
    /// <summary>The local-id prefix of the named path block.</summary>
    private const string PathPrefix = "sys/path/";

    /// <summary>Case count of the corpus before the path block (SEM-2B review, 2026-10-23: 239).</summary>
    private const int PreexistingCaseCount = 239;

    /// <summary>
    /// SHA-256 over <see cref="CanonicalLine"/> of every pre-existing case, in corpus order, computed
    /// on <c>fb1a35e6</c> BEFORE the path block was added. A change here means an existing id now
    /// renders a different program or expectation, which needs a recipe-version bump instead.
    /// </summary>
    private const string PreexistingDigest = "sha256:2a74e128f6e935b6801a9a15da5390a5536ecdf1a10ea8e324909b69bbedbc07";

    private static IEnumerable<SemanticCase> PathCases
        => SemanticGrammarCorpusTests.Cases.Where(c => LocalId(c).StartsWith(PathPrefix, StringComparison.Ordinal));

    [Fact]
    public void ExistingIds_KeepTheirSourcesAndExpectations_AndTheBlockAddsOnlyPathIds()
    {
        var all = SemanticGrammarCorpusTests.Cases;
        var preexisting = all.Where(c => !LocalId(c).StartsWith(PathPrefix, StringComparison.Ordinal)).ToList();
        Assert.Equal(PreexistingCaseCount, preexisting.Count);
        var digest = Digest(preexisting);
        Assert.True(digest == PreexistingDigest, $"pre-existing cases changed: digest {digest}, pinned {PreexistingDigest}");

        // The block is appended after every systematic case and before the seeded tier, and ids stay unique.
        var systematic = SemanticCorpus.Systematic();
        var firstPath = systematic.ToList().FindIndex(c => LocalId(c).StartsWith(PathPrefix, StringComparison.Ordinal));
        Assert.True(firstPath > 0, "the corpus has no sys/path/ case");
        Assert.All(systematic.Skip(firstPath), c => Assert.StartsWith(PathPrefix, LocalId(c), StringComparison.Ordinal));
        Assert.Equal(all.Count, all.Select(c => c.CaseId).Distinct(StringComparer.Ordinal).Count());

        // Every path id is reconstructible from its durable id alone, and rebuilds the same case.
        foreach (var semanticCase in PathCases)
        {
            Assert.True(SemanticCorpus.TryReconstruct(semanticCase.CaseId, SemanticRecipe.RecipeVersion, out var rebuilt, out var problem), problem);
            Assert.Equal(CanonicalLine(semanticCase), CanonicalLine(rebuilt));
        }
    }

    /// <summary>
    /// Every path case names the path it was built for (<c>sys/path/&lt;Path&gt;/…</c>), claims it, and
    /// has EVERY evidence-backed claim admitted: no rejected claim, nothing claimed but not exercised.
    /// </summary>
    [Fact]
    public void EveryPathCase_HasItsClaimedPathsAdmittedOnEvidence()
    {
        var failures = new List<string>();
        foreach (var semanticCase in PathCases)
        {
            var named = NamedPath(semanticCase);
            if (!semanticCase.Paths.HasFlag(named)) failures.Add($"{semanticCase.CaseId}: does not claim {named}");
            var result = SemanticGrammarCorpusTests.ResultOf(semanticCase);
            if (!result.PathRejections.IsEmpty)
                failures.Add($"{semanticCase.CaseId}: rejected claims [{string.Join("; ", result.PathRejections)}]");
            var claimed = semanticCase.Paths & SemanticPath.EvidenceBacked;
            if ((result.PathsExercised & claimed) != claimed)
                failures.Add($"{semanticCase.CaseId}: claimed {claimed}, exercised {result.PathsExercised & SemanticPath.EvidenceBacked}");
            if (!result.PathsExercised.HasFlag(named)) failures.Add($"{semanticCase.CaseId}: {named} not in PathsExercised");
        }

        Assert.True(failures.Count == 0, string.Join(Environment.NewLine, failures));
    }

    /// <summary>Each thin path gets at least eight named cases, each a distinct program.</summary>
    [Fact]
    public void EveryThinPath_HasEightDistinctNamedShapes()
    {
        foreach (var path in new[] { SemanticPath.LoopShortCircuit, SemanticPath.LoopFallback, SemanticPath.GenericInsideOptimizedLoop })
        {
            var cases = PathCases.Where(c => NamedPath(c) == path).ToList();
            Assert.True(cases.Count >= 8, $"{path} has {cases.Count} named path cases (want at least 8)");
            Assert.Equal(cases.Count, cases.Select(c => c.Source).Distinct(StringComparer.Ordinal).Count());
        }
    }

    /// <summary>
    /// The per-path loop floor is real: without the path block the corpus violates it for the thin
    /// paths with the honest count message, and with it every loop path meets the floor.
    /// </summary>
    [Fact]
    public void LoopPathFloor_FailsWithoutThePathBlock_AndHoldsWithIt()
    {
        var withoutBlock = SemanticCoverage.Of(SemanticGrammarCorpusTests.Cases
            .Where(c => !LocalId(c).StartsWith(PathPrefix, StringComparison.Ordinal))
            .Select(c => (c, SemanticGrammarCorpusTests.ResultOf(c))));
        var violations = withoutBlock.Floors(SemanticCorpus.RequiredInteractions);
        Assert.Contains(violations, v => v.StartsWith($"intended path {SemanticPath.LoopShortCircuit} has ", StringComparison.Ordinal)
            && v.EndsWith($"exercised cases (floor {SemanticCoverage.LoopPathFloor})", StringComparison.Ordinal));

        var full = SemanticCoverage.Of(SemanticGrammarCorpusTests.Cases.Select(c => (c, SemanticGrammarCorpusTests.ResultOf(c))));
        foreach (var path in SemanticCoverage.LoopPathFloors)
        {
            var count = full.PathsExercised.GetValueOrDefault(path.ToString());
            Assert.True(count >= SemanticCoverage.LoopPathFloor, $"{path}: {count} exercised cases (floor {SemanticCoverage.LoopPathFloor})");
        }
    }

    private static string LocalId(SemanticCase c) => c.CaseId[SemanticRecipe.CasePrefix.Length..];

    private static SemanticPath NamedPath(SemanticCase c)
    {
        var parts = LocalId(c).Split('/');
        Assert.True(parts.Length >= 4 && Enum.TryParse<SemanticPath>(parts[2], out var path) && path != SemanticPath.None,
            $"{c.CaseId} does not name its path as sys/path/<Path>/<variant>");
        return Enum.Parse<SemanticPath>(parts[2]);
    }

    /// <summary>Everything durable about a case except build provenance (which names the commit).</summary>
    internal static string CanonicalLine(SemanticCase c)
    {
        var e = c.Expected;
        var text = new StringBuilder();
        void Field(string name, string? value) => text.Append(name).Append('=').Append(value ?? "<null>").Append('\u001F');
        Field("id", c.CaseId);
        Field("tier", c.Tier);
        Field("seed", c.Seed?.ToString("X", CultureInfo.InvariantCulture));
        Field("index", c.Index?.ToString(CultureInfo.InvariantCulture));
        Field("families", string.Join(",", c.Families));
        Field("features", string.Join(",", c.Features));
        foreach (var member in c.Members) Field("member:" + member.Role, member.Source);
        Field("profiles", string.Join(",", c.Profiles));
        Field("kind", e.Kind.ToString());
        Field("value", e.ValueIdentity);
        Field("emitted", e.EmittedCount?.ToString(CultureInfo.InvariantCulture));
        Field("error", e.ErrorCategory);
        Field("diagnostic", e.Diagnostic?.ToString());
        Field("phase", e.DiagnosticPhase);
        Field("events", string.Join(",", e.Events));
        Field("cancelled", string.Join(",", e.CancelledEventsPrefix));
        Field("paths", c.Paths.ToString());
        Field("minimumCacheHits", c.MinimumCacheHits.ToString(CultureInfo.InvariantCulture));
        return text.ToString();
    }

    internal static string Digest(IEnumerable<SemanticCase> cases)
        => SemanticFingerprint.Of(string.Join("\n", cases.Select(CanonicalLine)));
}
