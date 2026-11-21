using System.Globalization;
using System.Text;
using System.Text.RegularExpressions;
using KatLang.ParserFuzz;

namespace KatLang.Tests;

/// <summary>
/// HOST-DIFF-1: generates and pins <c>lean/CoreTests/HostParentDifferential.lean</c>, the Lean/C#
/// differential corpus of HOST-BUILT ASTs with pre-wired <see cref="ScopeCtx"/> parent chains
/// (<see cref="HostParentDifferentialCorpus"/>). For every case the ONE constructed program graph is
/// evaluated by C# on every route (<see cref="HostParentDifferentialHarness"/>) and encoded for Lean
/// by <see cref="LeanAstEncoder"/>; the artifact guards Lean's neutral observation and published
/// zero-argument cache entries against the recorded C# ones, on success and on failure alike
/// (KL-06), and, on success, the Lean exporter's <c>kl-struct-v1</c> text of the value against the C#
/// encoder's text of the C# value (KL-07 pilot, <see cref="StructuralIdentityExamples"/>); <c>lake build CoreTests</c>
/// compiles it (it is imported by <c>lean/CoreTests.lean</c>). Every case is comparable: HOST-LEAN-O6 gave
/// every host level its object's Lean host-scope token, which retired the last known model divergence
/// (HP-14b). A future reviewed divergence would be excluded from the comparable partition and pinned on
/// both sides instead.
///
/// Regenerate with:
///   $env:KATLANG_REGENERATE_HOST_PARENT_DIFFERENTIAL = "1"
///   dotnet test --filter HostParentDifferential
/// That run writes the artifact and then fails by design (see <see cref="ArtifactRegeneration"/>);
/// review the diff, clear the flag, rerun, and run <c>lake build CoreTests</c>.
/// </summary>
public class HostParentDifferentialTests
{
    private const string ArtifactRelativePath = "lean/CoreTests/HostParentDifferential.lean";

    [Fact]
    public void GeneratedLeanArtifact_MatchesCurrentCSharpObservations()
    {
        var expected = GenerateArtifact();
        var path = Path.Combine(RepoRoot.Find(), ArtifactRelativePath);
        var flag = RegenerationFlags.HostParentDifferential;

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
                    $"{ArtifactRelativePath} is out of date with the host-parent corpus or the current C# observations. " +
                    $"Set {flag}=1 and rerun this test to regenerate it (that run fails by design), review the diff, and run " +
                    "`lake build CoreTests` to check the Lean side. " +
                    SemanticExplorerLeanArtifactTests.DescribeFirstDifference(expected, actual));
            },
            afterRegenerating: "run `lake build CoreTests` to check the Lean side");
    }

    [Fact]
    public void GeneratedModule_IsImportedByTheCanonicalCoreTestsTarget()
    {
        var root = File.ReadAllText(Path.Combine(RepoRoot.Find(), "lean/CoreTests.lean")).ReplaceLineEndings("\n");
        Assert.Contains("\nimport CoreTests.HostParentDifferential\n", root, StringComparison.Ordinal);
    }

    /// <summary>Stable, unique ids; every HP-01..HP-14 family of the HOST-DIFF-1 matrix is present, plus DECON-CACHE-2's HP-15, KL-06's HP-16, KL-07's HP-17 and EXPORTED-DETACHED's HP-18.</summary>
    [Fact]
    public void CorpusIds_AreStableUnique_AndCoverTheWholeMatrix()
    {
        var cases = HostParentDifferentialCorpus.AllCases();
        Assert.All(cases, c => Assert.Matches("^HP-[0-9]{2}[a-z]$", c.Id));
        Assert.Equal(cases.Count, cases.Select(c => c.Id).Distinct(StringComparer.Ordinal).Count());
        Assert.Equal(cases.Count, cases.Select(c => c.LeanName).Distinct(StringComparer.Ordinal).Count());
        var families = cases.Select(c => c.Id[..5]).Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToList();
        Assert.Equal(Enumerable.Range(1, 18).Select(n => $"HP-{n:00}"), families);
        Assert.All(cases, c => Assert.False(string.IsNullOrWhiteSpace(c.Description), c.Id));
    }

    /// <summary>
    /// The comparable / divergent partition is exact and reviewed: a case can leave the comparable
    /// partition only by being named here with its machine-checked divergence. Since HOST-LEAN-O6 the
    /// divergent partition is EMPTY: HP-14b (O6-18, Q-19 over empty host levels) is comparable.
    /// </summary>
    [Fact]
    public void Partition_DivergentCasesAreExactlyTheReviewedHostLeanO6Shapes()
    {
        var divergent = HostParentDifferentialCorpus.AllCases().Where(c => c.Divergence is not null)
            .Select(c => c.Id).ToList();
        Assert.Empty(divergent);
        Assert.All(HostParentDifferentialCorpus.AllCases().Where(c => c.Divergence is not null), c =>
        {
            Assert.False(string.IsNullOrWhiteSpace(c.Divergence!.Reason), c.Id);
            Assert.Contains("HOST-LEAN-O6", c.Divergence.Reason, StringComparison.Ordinal);
            Assert.NotEqual(c.Divergence.CSharpNeutral, c.Divergence.LeanNeutral);
        });
    }

    /// <summary>
    /// The pinned coverage floors: the CURRENT counts of the corpus. They may only be RAISED (or
    /// lowered in a reviewed diff that deliberately removes cases); the coverage-drop controls
    /// (<see cref="CoverageDropControl_LosingOneUnitOfAMetricFailsTheRatchet"/>) fail while a floor
    /// is below its current count, so a floor cannot go stale after cases are added.
    /// </summary>
    private const int MinimumComparableCases = 134;
    private const int MinimumComparableCasesWithPreWiredParents = 124;
    private const int MinimumSuccessCacheGuards = 200;

    private const string ComparableMetric = "comparable";
    private const string PreWiredMetric = "pre-wired";
    private const string SuccessCacheGuardMetric = "success-cache-guards";

    /// <summary>The three ratcheted metrics of a case list; cache guards are read back from the GENERATED text.</summary>
    private sealed record HostParentCoverage(int Comparable, int PreWired, int SuccessCacheGuards);

    private static bool HasPreWiredParent(HostParentCase hostCase)
        => LeanAstEncoder.EncodeExpr(hostCase.Program).Contains("Algorithm.withParent (some ", StringComparison.Ordinal);

    private static HostParentCoverage MeasureCoverage(IReadOnlyList<HostParentCase> cases)
    {
        var comparable = cases.Where(c => c.Divergence is null).ToList();
        var wired = comparable.Count(HasPreWiredParent);
        var successes = comparable.Where(c => HostParentDifferentialHarness.Observe(c).IsSuccess).ToList();
        var guards = EmittedCacheGuards.Parse(GenerateArtifact(cases));
        Assert.All(successes, c => Assert.Single(guards.Totals(c.LeanName)));
        var cacheGuards = successes.Sum(c => guards.Names(c.LeanName).Select(g => g.Name).Distinct(StringComparer.Ordinal).Count());
        return new(comparable.Count, wired, cacheGuards);
    }

    /// <summary>The metrics of <paramref name="coverage"/> that are below their pinned floor, each with its message.</summary>
    private static List<(string Metric, string Message)> CoverageShortfalls(HostParentCoverage coverage)
    {
        var shortfalls = new List<(string Metric, string Message)>();
        if (coverage.Comparable < MinimumComparableCases)
        {
            shortfalls.Add((ComparableMetric,
                $"Comparable host-parent differential coverage shrank below {MinimumComparableCases} (actual {coverage.Comparable})."));
        }

        if (coverage.PreWired < MinimumComparableCasesWithPreWiredParents)
        {
            shortfalls.Add((PreWiredMetric,
                $"Comparable cases with an encoded pre-wired parent shrank below {MinimumComparableCasesWithPreWiredParents} (actual {coverage.PreWired})."));
        }

        if (coverage.SuccessCacheGuards < MinimumSuccessCacheGuards)
        {
            shortfalls.Add((SuccessCacheGuardMetric,
                $"Per-property cache guards on successful cases shrank below {MinimumSuccessCacheGuards} (actual {coverage.SuccessCacheGuards})."));
        }

        return shortfalls;
    }

    /// <summary>
    /// Coverage ratchet: an encoder regression cannot pass silently — a case that stops encoding
    /// fails generation loudly — and a case moved to the divergent partition breaks the exact id
    /// list above. Cache guards are read back from the GENERATED artifact: the SUCCESS floor is
    /// pinned here, and failing cases by exact enumeration
    /// (<see cref="FidelityRatchet_ComparableFailuresKeepTheirPublicationGuards"/>, KL-06).
    /// </summary>
    [Fact]
    public void FidelityRatchet_ComparableHostParentCoverageCannotSilentlyShrink()
    {
        var shortfalls = CoverageShortfalls(MeasureCoverage(HostParentDifferentialCorpus.AllCases()));
        Assert.True(shortfalls.Count == 0, string.Join(" ", shortfalls.Select(s => s.Message)));
    }

    /// <summary>
    /// Coverage-drop controls, one per ratcheted metric. Each takes ONE unit of exactly one metric
    /// away from the current corpus (in memory; the corpus is untouched) and requires the ratchet to
    /// report exactly that metric:
    /// <list type="bullet">
    /// <item><c>comparable</c>: HP-16a is removed. It fails and has no pre-wired parent, so only the
    /// comparable count drops.</item>
    /// <item><c>pre-wired</c>: HP-02f keeps its id but runs HP-16a's parent-free program. Both fail,
    /// so the comparable count and the success cache guards stay as they are.</item>
    /// <item><c>success-cache-guards</c>: HP-10g stops watching <c>Large</c>, a property it never
    /// publishes, which removes that one named guard and nothing else.</item>
    /// </list>
    /// A floor below the current count absorbs the drop, so a control also fails whenever its floor
    /// is stale: raise the floor to the count the message reports.
    /// </summary>
    [Theory]
    [InlineData(ComparableMetric)]
    [InlineData(PreWiredMetric)]
    [InlineData(SuccessCacheGuardMetric)]
    public void CoverageDropControl_LosingOneUnitOfAMetricFailsTheRatchet(string metric)
    {
        var all = HostParentDifferentialCorpus.AllCases();
        HostParentCase Named(string id) => all.Single(c => c.Id == id);
        var failingWithoutParent = Named("HP-16a");
        var failingWithParent = Named("HP-02f");
        var watchingAnUnpublishedName = Named("HP-10g");

        // The premises that make each drop hit one metric only.
        Assert.False(HostParentDifferentialHarness.Observe(failingWithoutParent).IsSuccess);
        Assert.False(HasPreWiredParent(failingWithoutParent));
        Assert.False(HostParentDifferentialHarness.Observe(failingWithParent).IsSuccess);
        Assert.True(HasPreWiredParent(failingWithParent));
        var watching = HostParentDifferentialHarness.Observe(watchingAnUnpublishedName);
        Assert.True(watching.IsSuccess);
        Assert.Contains("Large", watchingAnUnpublishedName.WatchedProperties);
        Assert.Equal(0, watching.Published("Large"));

        IReadOnlyList<HostParentCase> reduced = metric switch
        {
            ComparableMetric => all.Where(c => c.Id != failingWithoutParent.Id).ToList(),
            PreWiredMetric => all.Select(c => c.Id == failingWithParent.Id ? c with { Program = failingWithoutParent.Program } : c).ToList(),
            SuccessCacheGuardMetric => all.Select(c => c.Id == watchingAnUnpublishedName.Id
                ? c with { WatchedProperties = c.WatchedProperties.Where(name => name != "Large").ToList() }
                : c).ToList(),
            _ => throw new ArgumentOutOfRangeException(nameof(metric), metric, "Unknown coverage metric."),
        };

        var current = MeasureCoverage(all);
        var dropped = MeasureCoverage(reduced);
        var expected = metric switch
        {
            ComparableMetric => current with { Comparable = current.Comparable - 1 },
            PreWiredMetric => current with { PreWired = current.PreWired - 1 },
            _ => current with { SuccessCacheGuards = current.SuccessCacheGuards - 1 },
        };
        Assert.Equal(expected, dropped);

        var shortfalls = CoverageShortfalls(dropped);
        Assert.True(shortfalls.Count == 1 && shortfalls[0].Metric == metric,
            $"Dropping one unit of '{metric}' ({current} -> {dropped}) must fail the ratchet on exactly that metric, but it reported " +
            $"[{string.Join(", ", shortfalls.Select(s => s.Metric))}]. A floor below the current count is stale: raise it to the current count.");
    }

    /// <summary>
    /// KL-06: every comparable case C# observes FAILING, enumerated by hand (not by the generator or
    /// the harness), with the names its cache guards compare: its watched properties plus every name
    /// C# published before the failure. HP-14i publishes <c>R</c> twice before failing; the HP-16
    /// witnesses are a failure after a publication, a failing owner chain and a failed owner with a
    /// published dependency (owner <c>Run</c> and dependency <c>P</c> both named).
    /// </summary>
    private static readonly (string Id, string[] Names)[] ExpectedFailureCacheGuardNames =
    [
        ("HP-02f", []), ("HP-03b", []), ("HP-03d", []),
        ("HP-05c", []), ("HP-05d", []), ("HP-05e", []), ("HP-05f", []), ("HP-05g", []), ("HP-05h", []), ("HP-05i", []), ("HP-05j", []),
        ("HP-08g", []), ("HP-08h", []), ("HP-08i", []), ("HP-08j", []),
        ("HP-13c", []), ("HP-13d", []), ("HP-13e", []), ("HP-13m", ["M"]),
        ("HP-14b", ["F"]), ("HP-14g", []), ("HP-14i", ["R"]), ("HP-14k", []), ("HP-14l", []), ("HP-14o", []),
        ("HP-14s", []), ("HP-14t", []), ("HP-14u", []),
        ("HP-16a", ["X"]), ("HP-16b", ["P", "Run"]), ("HP-16c", ["P", "Run"]),
        // EXPORTED-DETACHED: the mis-exposed trees are refused, and publish nothing under the false key.
        ("HP-18a", ["P"]), ("HP-18b", ["P"]), ("HP-18c", ["P"]), ("HP-18d", ["P"]), ("HP-18e", ["P"]), ("HP-18f", ["P"]),
        ("HP-18g", ["P", "Q"]), ("HP-18h", ["P", "Q"]), ("HP-18i", ["L", "P"]),
        // The other executed parameter operations: invoked and transported, detached and static.
        ("HP-18l", ["P"]), ("HP-18n", ["P"]), ("HP-18p", []), ("HP-18q", []),
        ("HP-18r", ["P"]), ("HP-18t", ["P"]),
    ];

    /// <summary>
    /// KL-06 coverage ratchet for FAILING cases, pinned separately from the success floor: the
    /// comparable failing cases are exactly <see cref="ExpectedFailureCacheGuardNames"/>, and for each
    /// the generated artifact keeps its error guards (the neutral <c>err</c> observation and, for a
    /// supported failure, the structured payload) plus ONE total guard and exactly one guard per
    /// expected name — zero counts and cases with no name included. A failing case cannot appear,
    /// vanish or lose a publication guard unreviewed.
    /// </summary>
    [Fact]
    public void FidelityRatchet_ComparableFailuresKeepTheirPublicationGuards()
    {
        var cases = HostParentDifferentialCorpus.AllCases();
        var failing = cases.Where(c => c.Divergence is null)
            .Select(c => (Case: c, Observation: HostParentDifferentialHarness.Observe(c)))
            .Where(pair => !pair.Observation.IsSuccess)
            .ToDictionary(pair => pair.Case.Id, StringComparer.Ordinal);
        Assert.Equal(ExpectedFailureCacheGuardNames.Select(e => e.Id).Order(StringComparer.Ordinal),
            failing.Keys.Order(StringComparer.Ordinal));

        var artifact = GenerateArtifact(cases);
        var lines = artifact.Split('\n');
        var guards = EmittedCacheGuards.Parse(artifact);
        foreach (var (id, names) in ExpectedFailureCacheGuardNames)
        {
            var (hostCase, observation) = failing[id];
            var lean = hostCase.LeanName;
            Assert.Single(lines, line => line.StartsWith($"#guard obs {lean} == \"err ", StringComparison.Ordinal));
            if (observation.ErrorPayload is not null)
                Assert.Single(lines, line => line.StartsWith($"#guard errorObs {lean} == .matched ", StringComparison.Ordinal));
            Assert.Equal(observation.PublishedTotal, Assert.Single(guards.Totals(lean)));
            var expected = names.Order(StringComparer.Ordinal).Select(name => (name, observation.Published(name)));
            Assert.Equal(expected, guards.Names(lean).OrderBy(g => g.Name, StringComparer.Ordinal));
        }
    }

    /// <summary>
    /// KL-06 witnesses with their reviewed C# observations: each fails with <c>div0</c>, keeps its
    /// structured payload, and has pinned published entries — a failure after a publication keeps
    /// <c>X</c>, a failing owner chain publishes nothing, a failed owner <c>Run</c> keeps its successful
    /// dependency <c>P</c>. The generator emits exactly these guard lines. Mutating only HP-16c's
    /// <c>P</c> count to zero fails that named Lean guard alone, its error guards still matching.
    /// </summary>
    [Theory]
    [InlineData("HP-16a", "X=1", 1)]
    [InlineData("HP-16b", "P=0 Run=0", 0)]
    [InlineData("HP-16c", "P=1 Run=0", 1)]
    public void FailedRunPublications_CSharpObservesTheReviewedEntries_AndTheArtifactGuardsThem(string id, string entries, int total)
    {
        var hostCase = HostParentDifferentialCorpus.AllCases().Single(c => c.Id == id);
        Assert.Null(hostCase.Divergence);
        var expected = entries.Split(' ').Select(entry => entry.Split('='))
            .Select(pair => (Name: pair[0], Count: int.Parse(pair[1], CultureInfo.InvariantCulture))).ToList();

        var observation = HostParentDifferentialHarness.Observe(hostCase);
        Assert.Equal("err div0", observation.Neutral);
        Assert.Equal(new SharedErrorPayload("div0", [], []), observation.ErrorPayload);
        Assert.All(expected, e => Assert.Equal(e.Count, observation.Published(e.Name)));
        Assert.Equal(total, observation.PublishedTotal);

        var lean = hostCase.LeanName;
        string[] expectedGuards =
        [
            $"#guard obs {lean} == \"err div0\"",
            $"#guard errorObs {lean} == .matched (some {{ kind := \"div0\", names := [], counts := [] }})",
            .. expected.Select(e => $"#guard cacheEntries {lean} \"{e.Name}\" == some {e.Count}"),
            $"#guard cacheTotal {lean} == some {total}",
        ];
        Assert.Equal(expectedGuards, GenerateArtifact([hostCase]).Split('\n').Where(line => line.StartsWith("#guard ", StringComparison.Ordinal)
            && line.Contains($" {lean} ", StringComparison.Ordinal)));
    }

    /// <summary>
    /// KL-07 pilot ratchet, read back from the GENERATED text: every comparable SUCCESSFUL case has
    /// exactly one <c>structural</c> guard, pinning the C# encoder's identity of its typed value (which
    /// decodes back to a value equal to the plain run's), and no failing case has one.
    /// </summary>
    [Fact]
    public void FidelityRatchet_EverySuccessfulCaseKeepsItsStructuralGuard()
    {
        const int MinimumStructuralGuards = 84;

        var cases = HostParentDifferentialCorpus.AllCases();
        var lines = GenerateArtifact(cases).Split('\n');
        var guards = lines.Where(line => line.StartsWith("#guard structural hp_", StringComparison.Ordinal)
            && line.Contains(" == some ", StringComparison.Ordinal)).ToList();
        var successes = 0;
        foreach (var hostCase in cases.Where(c => c.Divergence is null))
        {
            var observation = HostParentDifferentialHarness.Observe(hostCase);
            var ofCase = guards.Where(line => line.StartsWith($"#guard structural {hostCase.LeanName} ", StringComparison.Ordinal)).ToList();
            if (!observation.IsSuccess)
            {
                Assert.Null(observation.StructuralIdentity);
                Assert.Empty(ofCase);
                continue;
            }

            successes++;
            var identity = Assert.IsType<string>(observation.StructuralIdentity);
            Assert.Equal($"#guard structural {hostCase.LeanName} == some {LeanAstEncoder.QuoteString(identity)}", Assert.Single(ofCase));
            Assert.True(MetamorphicStructuralIdentity.TryDecode(identity, out var decoded, out var problem), $"{hostCase.Id}: {problem}");
            Assert.True(Result.ValueComparer.Equals(Evaluator.Run(hostCase.Program).Value, decoded), hostCase.Id);
        }

        Assert.Equal(successes, guards.Count);
        Assert.True(successes >= MinimumStructuralGuards,
            $"Structural guards on successful host-parent cases shrank below {MinimumStructuralGuards} (actual {successes}).");
    }

    /// <summary>
    /// KL-07 acceptance, C# half: HP-17a (the two strings <c>a</c>, <c>b</c>) and HP-17b (the ONE
    /// host-built string <c>a', 'b</c>) are different values with one neutral text and the reviewed
    /// identities. The generated artifact pins that neutral text on both, their distinct identities, and
    /// guards that neither Lean value has the other's identity. Substituting either program for the
    /// other in a scratch copy of the artifact fails the structural guard while the neutral guard
    /// still passes (recorded in <c>docs/design/differential-observations.md</c>).
    /// </summary>
    [Fact]
    public void NeutralCollisionPair_SharesTheNeutralTextButNotTheIdentity()
    {
        var twoStrings = HostParentDifferentialCorpus.AllCases().Single(c => c.Id == "HP-17a");
        var oneString = HostParentDifferentialCorpus.AllCases().Single(c => c.Id == "HP-17b");
        Assert.Equal([("HP-17a", "HP-17b")], HostParentDifferentialCorpus.NeutralCollisionPairs);
        Assert.False(Result.ValueComparer.Equals(Evaluator.Run(twoStrings.Program).Value, Evaluator.Run(oneString.Program).Value));

        var left = HostParentDifferentialHarness.Observe(twoStrings);
        var right = HostParentDifferentialHarness.Observe(oneString);
        Assert.Equal("ok raw=L['a', 'b'] n=1", left.Neutral);
        Assert.Equal(left.Neutral, right.Neutral);
        Assert.Equal("kl-struct-v1:3:t1:at1:bl2:0,1,;", left.StructuralIdentity);
        Assert.Equal("kl-struct-v1:2:t6:a', 'bl1:0,;", right.StructuralIdentity);

        string[] expected =
        [
            "#guard obs hp_17a == \"ok raw=L['a', 'b'] n=1\"",
            "#guard structural hp_17a == some \"kl-struct-v1:3:t1:at1:bl2:0,1,;\"",
            "#guard obs hp_17b == \"ok raw=L['a', 'b'] n=1\"",
            "#guard structural hp_17b == some \"kl-struct-v1:2:t6:a', 'bl1:0,;\"",
            "#guard structural hp_17a != some \"kl-struct-v1:2:t6:a', 'bl1:0,;\"",
            "#guard structural hp_17b != some \"kl-struct-v1:3:t1:at1:bl2:0,1,;\"",
        ];
        Assert.Equal(expected, GenerateArtifact([twoStrings, oneString]).Split('\n')
            .Where(line => line.StartsWith("#guard obs ", StringComparison.Ordinal) || line.StartsWith("#guard structural ", StringComparison.Ordinal)));
    }

    /// <summary>
    /// The C# half of each known divergence: the C# routes observe exactly the reviewed C# value, and
    /// it differs from the Lean value the generated artifact pins, so neither side can drift into a
    /// fake agreement (or a different disagreement) unnoticed.
    /// </summary>
    [Fact]
    public void KnownDivergences_CSharpObservesExactlyTheReviewedValue()
    {
        foreach (var hostCase in HostParentDifferentialCorpus.AllCases().Where(c => c.Divergence is not null))
        {
            var observation = HostParentDifferentialHarness.Observe(hostCase);
            Assert.Equal(hostCase.Divergence!.CSharpNeutral, observation.Neutral);
        }
    }

    /// <summary>Encoding is a pure function of the graph: two encodings of one case are identical.</summary>
    [Fact]
    public void Encoding_IsDeterministic_AndEveryCaseEncodes()
    {
        foreach (var hostCase in HostParentDifferentialCorpus.AllCases())
            Assert.Equal(LeanAstEncoder.EncodeExpr(hostCase.Program), LeanAstEncoder.EncodeExpr(hostCase.Program));
    }

    /// <summary>
    /// Declaration fidelity of the encoded corpus itself (HOST-LEAN-O6): a property declared in a host
    /// level carries ONE declaration identity per property OBJECT — the one-object cases (HP-09a,
    /// HP-12c) and the distinct-object cases that share a property, a list or a record copy (HP-08b..d)
    /// alike, the declaring OBJECT being the host token instead (<see cref="HostScopeTokens_FollowScopeObjectIdentity"/>)
    /// — and the fresh-object case (HP-08a) none at all.
    /// </summary>
    [Theory]
    [InlineData("HP-09a", 1, 2)]
    [InlineData("HP-12c", 4, 8)]
    [InlineData("HP-08b", 1, 2)]
    [InlineData("HP-08c", 1, 2)]
    [InlineData("HP-08d", 1, 2)]
    [InlineData("HP-08a", 0, 0)]
    public void HostScopeIdentities_FollowObjectIdentity(string id, int distinctIds, int occurrences)
    {
        var hostCase = HostParentDifferentialCorpus.AllCases().Single(c => c.Id == id);
        var encoded = LeanAstEncoder.EncodeExpr(hostCase.Program);
        var hostLevelIds = Regex.Matches(encoded, @"ScopeCtx\.mk none \[\] \[\] \[(?<props>.*?)\] \[\] \[\] none \(some \(\.host \d+\)\)")
            .SelectMany(m => Regex.Matches(m.Groups["props"].Value, @"identity := some \(\.shared (\d+)\)").Select(x => x.Groups[1].Value))
            .ToList();
        Assert.Equal(occurrences, hostLevelIds.Count);
        Assert.Equal(distinctIds, hostLevelIds.Distinct(StringComparer.Ordinal).Count());
    }

    /// <summary>
    /// HOST-LEAN-O6 encoder fidelity of the corpus itself: the encoded program carries exactly one Lean
    /// host-scope token per original host <see cref="ScopeCtx"/> OBJECT it reaches — one object
    /// reached through several edges (HP-09a, HP-12c, HP-14a, HP-14f) is one token, distinct objects
    /// (fresh, record copies, levels sharing a list or a property, empty levels, ancestors) are
    /// distinct tokens.
    /// </summary>
    [Theory]
    [InlineData("HP-09a", 1)]
    [InlineData("HP-09b", 3)]
    [InlineData("HP-12c", 1)]
    [InlineData("HP-12d", 2)]
    [InlineData("HP-08d", 2)]
    [InlineData("HP-08e", 4)]
    [InlineData("HP-14a", 1)]
    [InlineData("HP-14b", 2)]
    [InlineData("HP-14e", 2)]
    [InlineData("HP-14f", 1)]
    [InlineData("HP-14i", 2)]
    [InlineData("HP-14j", 1)]
    public void HostScopeTokens_FollowScopeObjectIdentity(string id, int tokens)
    {
        var hostCase = HostParentDifferentialCorpus.AllCases().Single(c => c.Id == id);
        var encoded = LeanAstEncoder.EncodeExpr(hostCase.Program);
        var distinct = Regex.Matches(encoded, @"\(some \(\.host (\d+)\)\)").Select(m => int.Parse(m.Groups[1].Value, CultureInfo.InvariantCulture))
            .Distinct().Order().ToList();
        Assert.Equal(Enumerable.Range(0, tokens), distinct);
    }

    /// <summary>
    /// HOST-LEAN-O6 migration and its new witnesses, with the reviewed C# observations. HP-14b was the
    /// pinned divergence (C# <c>err ambiguousOpen</c>, Lean <c>ok raw=7 n=1</c>); its C# expectation is
    /// UNCHANGED and Lean now agrees through the generated guard. HP-14e/g/i separate identities that only
    /// an empty host ANCESTOR distinguishes (cache owner, NEED-04 callable, runtime-alias binding cell);
    /// HP-14f/h/j are their one-object controls.
    /// </summary>
    [Theory]
    [InlineData("HP-14a", "ok raw=7 n=1")]
    [InlineData("HP-14b", "err ambiguousOpen")]
    [InlineData("HP-14e", "ok raw=S[1, 2] n=2")]
    [InlineData("HP-14f", "ok raw=S[1, 1] n=2")]
    [InlineData("HP-14g", "err type")]
    [InlineData("HP-14h", "ok raw=0 n=1")]
    [InlineData("HP-14i", "err type")]
    [InlineData("HP-14j", "ok raw=0 n=1")]
    [InlineData("HP-14k", "err type")]
    [InlineData("HP-14l", "err type")]
    [InlineData("HP-14m", "ok raw=0 n=1")]
    [InlineData("HP-14n", "ok raw=0 n=1")]
    [InlineData("HP-14o", "err ambiguousOpen")]
    [InlineData("HP-14p", "ok raw=7 n=1")]
    [InlineData("HP-14q", "ok raw=S[7, 7] n=2")]
    [InlineData("HP-14r", "ok raw=S[7, 7] n=2")]
    public void HostLeanO6Cases_CSharpObservesTheReviewedValue(string id, string expected)
    {
        var hostCase = HostParentDifferentialCorpus.AllCases().Single(c => c.Id == id);
        Assert.Null(hostCase.Divergence);
        Assert.Equal(expected, HostParentDifferentialHarness.Observe(hostCase).Neutral);
    }

    /// <summary>
    /// KL-04: HP-05j and HP-05k differ ONLY in absent versus explicitly empty exact-owner metadata on
    /// a member naming an input no level binds. C# refuses the first (structured LocalOnlyProperty
    /// payload) and returns 7 for the second, so their encodings must differ exactly there: the
    /// generated guards then pin Lean's outcome on each to these reviewed C# observations.
    /// </summary>
    [Fact]
    public void ExactOwnerListPresence_CasesKeepDistinctEncodingsAndReviewedObservations()
    {
        var absent = HostParentDifferentialCorpus.AllCases().Single(c => c.Id == "HP-05j");
        var empty = HostParentDifferentialCorpus.AllCases().Single(c => c.Id == "HP-05k");
        Assert.Null(absent.Divergence);
        Assert.Null(empty.Divergence);

        var refused = HostParentDifferentialHarness.Observe(absent);
        Assert.Equal("err localOnlyProperty", refused.Neutral);
        Assert.Equal(new SharedErrorPayload("localOnlyProperty", ["L", "captured"], []), refused.ErrorPayload);
        var accepted = HostParentDifferentialHarness.Observe(empty);
        Assert.Equal("ok raw=7 n=1", accepted.Neutral);
        Assert.Null(accepted.ErrorPayload);

        Assert.NotEqual(LeanAstEncoder.EncodeExpr(absent.Program), LeanAstEncoder.EncodeExpr(empty.Program));
        Assert.Equal(
            "(.algorithmExpr (alg [] [] [privateProp \"Box\" (alg [] [] "
            + "[publicLocalProp \"L\" (.localCapturedAncestorParams [\"absent\"]) (alg [] [] [] [.num 7])] [])] "
            + "[(.dotCall (.resolve \"Box\") \"L\" none)]))",
            LeanAstEncoder.EncodeExpr(absent.Program));
        Assert.Equal(
            "(.algorithmExpr (alg [] [] [privateProp \"Box\" (alg [] [] "
            + "[{ (publicLocalProp \"L\" (.localCapturedAncestorParams [\"absent\"]) (alg [] [] [] [.num 7])) with requiredOwnerDepths := some [] }] [])] "
            + "[(.dotCall (.resolve \"Box\") \"L\" none)]))",
            LeanAstEncoder.EncodeExpr(empty.Program));
    }

    /// <summary>
    /// The cache guards a generated artifact emits per Lean case name, read back from its TEXT so the
    /// ratchets pin what was generated. A <c>#guard cache…</c> line of any other shape fails loudly.
    /// </summary>
    private sealed class EmittedCacheGuards
    {
        private static readonly Regex EntriesLine = new(
            @"^#guard cacheEntries (?<case>hp_[0-9]{2}[a-z]) ""(?<name>[^""]+)"" == some (?<count>[0-9]+)$", RegexOptions.CultureInvariant);
        private static readonly Regex TotalLine = new(
            @"^#guard cacheTotal (?<case>hp_[0-9]{2}[a-z]) == some (?<count>[0-9]+)$", RegexOptions.CultureInvariant);

        private readonly Dictionary<string, List<(string Name, int Count)>> _names = new(StringComparer.Ordinal);
        private readonly Dictionary<string, List<int>> _totals = new(StringComparer.Ordinal);

        public static EmittedCacheGuards Parse(string artifact)
        {
            var guards = new EmittedCacheGuards();
            foreach (var line in artifact.Split('\n').Where(line => line.StartsWith("#guard cache", StringComparison.Ordinal)))
            {
                if (EntriesLine.Match(line) is { Success: true } entries)
                {
                    Add(guards._names, entries.Groups["case"].Value,
                        (entries.Groups["name"].Value, int.Parse(entries.Groups["count"].Value, CultureInfo.InvariantCulture)));
                }
                else if (TotalLine.Match(line) is { Success: true } total)
                    Add(guards._totals, total.Groups["case"].Value, int.Parse(total.Groups["count"].Value, CultureInfo.InvariantCulture));
                else
                    throw new InvalidOperationException($"Unrecognized cache guard line in the generated artifact: {line}");
            }

            return guards;
        }

        public IReadOnlyList<(string Name, int Count)> Names(string leanName) => _names.GetValueOrDefault(leanName) ?? [];
        public IReadOnlyList<int> Totals(string leanName) => _totals.GetValueOrDefault(leanName) ?? [];

        private static void Add<T>(Dictionary<string, List<T>> map, string key, T value)
        {
            if (!map.TryGetValue(key, out var list))
                map[key] = list = [];
            list.Add(value);
        }
    }

    /// <summary>
    /// An encoder refusal while generating names the case and keeps the encoder's precise reason:
    /// a case can never silently drop out, encode an empty parent, or be skipped as "not
    /// Lean-representable" (there is no catch-and-skip anywhere in generation).
    /// </summary>
    [Fact]
    public void Generation_NamesTheCaseAndTheShape_WhenTheEncoderRefuses()
    {
        var owned = new ScopeCtx(null, [], []) { Owner = new Algorithm.User(null, [], [], [], []) };
        var program = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [new Expr.AlgorithmExpr(new Algorithm.User(owned, [], [], [], []))], [], [new Expr.Num(1)]));
        var ex = Assert.Throws<InvalidOperationException>(() => GenerateArtifact([new HostParentCase("HP-99z", "evaluator-owned parent", program, [])]));
        Assert.Contains("HP-99z", ex.Message, StringComparison.Ordinal);
        Assert.Contains("evaluator-created ScopeCtx", ex.Message, StringComparison.Ordinal);
    }

    internal static string GenerateArtifact() => GenerateArtifact(HostParentDifferentialCorpus.AllCases());

    private static string EncodeCase(HostParentCase hostCase)
    {
        try
        {
            return LeanAstEncoder.EncodeExpr(hostCase.Program);
        }
        catch (NotSupportedException ex)
        {
            throw new InvalidOperationException(
                $"Host-parent case '{hostCase.Id}' ({hostCase.Description}) is not Lean-encodable: {ex.Message}", ex);
        }
    }

    internal static string GenerateArtifact(IReadOnlyList<HostParentCase> cases)
    {
        var comparableExpected = cases.Count(c => c.Divergence is null);
        var divergentExpected = cases.Count - comparableExpected;

        var builder = new StringBuilder();
        builder.Append($"""
            import KatLang
            import CoreTests.StructuralIdentity

            /-!
            GENERATED FILE - DO NOT EDIT BY HAND.

            HOST-DIFF-1: Lean/C# differential corpus of HOST-BUILT ASTs with pre-wired `ScopeCtx`
            parent chains (tests/KatLang.Tests/HostParentDifferential/HostParentDifferentialCorpus.cs).
            Each program below is `LeanAstEncoder`'s encoding of the SAME constructed C# AST the C#
            evaluator ran on every route (plain, counted, generic, optimized, suspending async); each
            `#guard` pins the C# neutral observation and the C# published zero-argument cache entries
            (per property name, and in total), on success and on failure alike (KL-06). A successful
            case's `structural` guard also pins the C# `kl-struct-v1` identity of its value against the
            Lean exporter's text (KL-07 pilot; `CoreTests/StructuralIdentity.lean`). A failing guard is
            a Lean/C# divergence on that case.

            Partition (machine-checked by the `*CaseIds.length` guards below):
            - corpus cases: {cases.Count}
            - comparable cases: {comparableExpected}
            - known HOST-LEAN-O6 divergences, pinned on both sides and excluded from comparison: {divergentExpected}

            Regenerate from the repo root with:
              $env:KATLANG_REGENERATE_HOST_PARENT_DIFFERENTIAL = "1"
              dotnet test .\KatLang.slnx --filter HostParentDifferential
            -/

            namespace HostParentDifferential
            open KatLang

            -- Compact graph terms contain sequential lets; this bounds elaboration of the
            -- accepted join-spine fixtures without changing any evaluator limit or observation.
            set_option maxRecDepth 4096

            """.ReplaceLineEndings("\n"));
        builder.Append('\n');
        builder.Append(LeanObsTemplate.SharedDefinitions.ReplaceLineEndings("\n"));
        builder.Append("\n\n");
        builder.Append(LeanObsTemplate.CacheObservationDefinitions.ReplaceLineEndings("\n"));
        builder.Append("\n\n");
        LeanObsTemplate.AppendCacheObservationContracts(builder);
        builder.Append("""
            /-- KL-07 pilot: the `kl-struct-v1` identity (`StructuralIdentity.encode`,
                `CoreTests/StructuralIdentity.lean`) of the value ONE plain run returns; `none` on
                failure. Each successful case's guard compares it with the C# encoder's text of the C#
                value (`MetamorphicStructuralIdentity.Encode`): unlike the neutral text, which writes
                strings between unescaped quotes, it never writes two different values alike. Every
                `#guard` is its own evaluation, so each structural guard runs its program once more. -/
            def structural (e : Expr) : Option String :=
              match runResult e with
              | .ok value => StructuralIdentity.encode value
              | .error _ => none

            -- Exporter cross-check (KL-07; StructuralIdentityExamples): every Lean-comparable example
            -- value was built by C# and is written here as a Lean literal; the expected text is the C#
            -- encoder's text of the C# value.

            """.ReplaceLineEndings("\n"));
        foreach (var example in StructuralIdentityExamples.LeanComparable)
        {
            builder.Append($"-- {example.Name}\n");
            builder.Append($"#guard StructuralIdentity.encode {StructuralIdentityExamples.LeanLiteral(example.Value)} == " +
                $"some {LeanAstEncoder.QuoteString(MetamorphicStructuralIdentity.Encode(example.Value))}\n");
        }

        builder.Append("\n\n");

        var comparableIds = new List<string>();
        var divergentIds = new List<string>();
        var comparableObservations = new Dictionary<string, (HostParentCase Case, HostParentObservation Observation)>(StringComparer.Ordinal);
        foreach (var hostCase in cases)
        {
            var program = EncodeCase(hostCase);
            var observation = HostParentDifferentialHarness.Observe(hostCase);
            if (hostCase.Divergence is { } divergence)
            {
                if (observation.Neutral != divergence.CSharpNeutral)
                {
                    throw new InvalidOperationException(
                        $"{hostCase.Id}: C# observes '{observation.Neutral}', not the reviewed divergence '{divergence.CSharpNeutral}'.");
                }

                builder.Append($"-- {hostCase.Id} [KNOWN DIVERGENCE - excluded from the comparable partition]: {hostCase.Description}\n");
                builder.Append($"-- Reason: {divergence.Reason}\n");
                builder.Append($"-- C# observes {divergence.CSharpNeutral} (pinned by HostParentDifferentialTests).\n");
                builder.Append($"def {hostCase.LeanName} : Expr :=\n  {program}\n");
                builder.Append($"#guard obs {hostCase.LeanName} == {LeanAstEncoder.QuoteString(divergence.LeanNeutral)}\n");
                builder.Append($"#guard obs {hostCase.LeanName} != {LeanAstEncoder.QuoteString(divergence.CSharpNeutral)}\n\n");
                divergentIds.Add(hostCase.Id);
                continue;
            }

            builder.Append($"-- {hostCase.Id}: {hostCase.Description}\n");
            builder.Append($"def {hostCase.LeanName} : Expr :=\n  {program}\n");
            builder.Append($"#guard obs {hostCase.LeanName} == {LeanAstEncoder.QuoteString(observation.Neutral)}\n");
            if (observation.IsSuccess)
            {
                // KL-07 pilot: the C# identity of the typed C# value against the Lean exporter's text.
                var identity = observation.StructuralIdentity
                    ?? throw new InvalidOperationException($"{hostCase.Id}: a successful observation has no structural identity.");
                builder.Append($"#guard structural {hostCase.LeanName} == some {LeanAstEncoder.QuoteString(identity)}\n");
            }

            LeanObsTemplate.AppendErrorGuard(builder, hostCase.LeanName, observation.ErrorPayload);
            // KL-06: publications are compared on success AND failure; a failed run keeps what its
            // successful owners published, and a watched name with no entry is guarded at zero.
            ZeroArgPublicationObserver.AppendCacheGuards(builder, hostCase.LeanName, hostCase.WatchedProperties, observation.Publications);
            builder.Append('\n');
            comparableIds.Add(hostCase.Id);
            comparableObservations.Add(hostCase.Id, (hostCase, observation));
        }

        AppendNeutralCollisionGuards(builder, comparableObservations);

        SemanticExplorerLeanArtifactTests.AppendCountGuard(builder, "comparableCaseIds", comparableIds, comparableExpected,
            "Machine-checked comparable partition count: the id list is built by the loop that emits the guards\n" +
            "above, while the expected total is computed independently from the corpus partition.");
        SemanticExplorerLeanArtifactTests.AppendCountGuard(builder, "divergentCaseIds", divergentIds, divergentExpected,
            "Machine-checked known-divergence partition count (HOST-LEAN-O6 shapes pinned on both sides).");
        builder.Append($"-- {comparableIds.Count} comparable cases, {divergentIds.Count} known divergences.\n");
        builder.Append("end HostParentDifferential\n");
        return builder.ToString();
    }

    /// <summary>
    /// KL-07 acceptance, for every declared pair (<see cref="HostParentDifferentialCorpus.NeutralCollisionPairs"/>)
    /// whose two cases are generated: both succeed with ONE neutral text but different identities
    /// (generation fails loudly otherwise), and each case's Lean value is guarded NOT to have the
    /// other case's C# identity. The per-case guards already pin the shared neutral text, so
    /// substituting one list for the other passes the neutral guard and fails the structural guard.
    /// </summary>
    private static void AppendNeutralCollisionGuards(
        StringBuilder builder, IReadOnlyDictionary<string, (HostParentCase Case, HostParentObservation Observation)> comparable)
    {
        foreach (var (leftId, rightId) in HostParentDifferentialCorpus.NeutralCollisionPairs)
        {
            if (!comparable.TryGetValue(leftId, out var left) || !comparable.TryGetValue(rightId, out var right))
                continue;
            if (!left.Observation.IsSuccess || !right.Observation.IsSuccess
                || left.Observation.Neutral != right.Observation.Neutral
                || left.Observation.StructuralIdentity == right.Observation.StructuralIdentity)
            {
                throw new InvalidOperationException(
                    $"KL-07 pair {leftId}/{rightId} must succeed with one neutral text and different identities: " +
                    $"'{left.Observation.Neutral}' {left.Observation.StructuralIdentity} vs " +
                    $"'{right.Observation.Neutral}' {right.Observation.StructuralIdentity}.");
            }

            builder.Append($"-- KL-07 acceptance ({leftId} / {rightId}): both values have the neutral text {left.Observation.Neutral},\n");
            builder.Append("-- pinned above, but different kl-struct-v1 identities: neither Lean value has the other's.\n");
            builder.Append($"#guard structural {left.Case.LeanName} != some {LeanAstEncoder.QuoteString(right.Observation.StructuralIdentity!)}\n");
            builder.Append($"#guard structural {right.Case.LeanName} != some {LeanAstEncoder.QuoteString(left.Observation.StructuralIdentity!)}\n\n");
        }
    }
}
