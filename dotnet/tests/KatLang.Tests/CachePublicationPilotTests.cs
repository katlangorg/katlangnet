using KatLang.ParserFuzz;
using KatLang.Tests.LanguageSpec;
using KatLang.Tests.SemanticTesting;

namespace KatLang.Tests;

/// <summary>
/// KL-06 pilots: the final-state zero-argument cache observation that the host-parent corpus
/// already compares (<see cref="HostParentDifferentialTests"/>), extended to ONE small pilot in each
/// of the three source corpora — the semantic explorer (<c>lean/SemanticExplorerCases.lean</c>), the
/// canonical language specification (<c>lean/LanguageSpecCases.lean</c>) and the SEM-2C generated
/// cases (<c>lean/CoreTests/SemanticGeneratedCases.lean</c>). Each pilot has four existing cases,
/// one per class (<see cref="CachePilotCase.Classes"/>): a success with entries, a success with an
/// empty cache, a failure after a publication and the pre-publication control. The existing
/// neutral, payload and count guards of the three artifacts are unchanged.
///
/// <para>Three publication states are kept apart everywhere (<see cref="CachePublicationState"/>):
/// NO observation (no guard; Lean <c>none</c>), a completed run with an EMPTY cache (<c>some 0</c>)
/// and a completed run with entries. These tests pin, by hand, the exact guard lines each generator
/// emits for its pilot, that no other program of the artifact has a cache guard, and that a wrong
/// reviewed expectation is refused by the C# observer used by the generators and the specification runner.</para>
/// </summary>
public class CachePublicationPilotTests
{
    private const string Explorer = "explorer";
    private const string Spec = "language-spec";
    private const string Generated = "generated";

    /// <summary>
    /// One corpus's pilot as the tests see it: the pilot cases, the generator, the ids of the BASE
    /// programs the artifact guards (computed here from the corpus, not read from the generator), the
    /// number of further guarded programs that are transformation members, and each pilot case's
    /// elaborated root with the Lean names of its transformation members.
    /// </summary>
    private sealed record Pilot(
        IReadOnlyList<CachePilotCase> Cases,
        Func<string> GenerateArtifact,
        IReadOnlyList<string> BaseProgramIds,
        int MemberPrograms,
        Func<string, (Algorithm Root, IReadOnlyList<string> MemberLeanNames)> Program,
        string CorpusLabel);

    private static Pilot Of(string corpus) => corpus switch
    {
        Explorer => new(
            SemanticExplorerLeanArtifactTests.CachePilotCases(),
            SemanticExplorerLeanArtifactTests.GenerateArtifact,
            [.. SemanticExplorerCorpus.AllCases().Where(c => c.LeanProgram is not null).Select(c => c.Id),
             .. SemanticExplorerCorpus.InternalNodeCases().Select(c => $"internal__{c.Id}")],
            0,
            id => (SourceProvenance.ParseValid(SemanticExplorerCorpus.AllCases().Single(c => c.Id == id).Source).Root, []),
            "Semantic-explorer differential"),
        Spec => new(
            LanguageSpecArtifactsTests.CachePilotCases(),
            LanguageSpecArtifactsTests.GenerateArtifact,
            LanguageSpecCorpus.AllCases().Where(c => c.IsLeanRepresentable).Select(c => c.Id).ToList(),
            0,
            id => (SourceProvenance.ParseValid(LanguageSpecCorpus.AllCases().Single(c => c.Id == id).Source).Root, []),
            "Language-spec"),
        Generated => new(
            SemanticGeneratedLeanArtifactTests.CachePilotCases(),
            SemanticGeneratedLeanArtifactTests.GenerateArtifact,
            SemanticGeneratedLeanArtifactTests.IncludedCases(SemanticCorpus.All()).Select(c => c.CaseId).ToList(),
            SemanticGeneratedLeanArtifactTests.IncludedCases(SemanticCorpus.All()).Sum(c => c.Members.Length - 1),
            id =>
            {
                var semanticCase = SemanticGeneratedLeanArtifactTests.IncludedCases(SemanticCorpus.All()).Single(c => c.CaseId == id);
                return (SemanticGeneratedLeanArtifactTests.ObserveMember(semanticCase, SemanticGeneratedLeanArtifactTests.BuildMember(semanticCase)).Root,
                    semanticCase.Members.Skip(1).Select(m => SemanticGeneratedLeanArtifactTests.MemberLeanName(id, m.Role)).ToList());
            },
            "SEM-2C differential"),
        _ => throw new ArgumentOutOfRangeException(nameof(corpus), corpus, "Unknown pilot corpus."),
    };

    private static readonly Dictionary<string, string> s_artifacts = new(StringComparer.Ordinal);

    /// <summary>One generation per corpus for the whole class (generation is deterministic).</summary>
    private static string[] ArtifactLines(string corpus)
    {
        lock (s_artifacts)
        {
            if (!s_artifacts.TryGetValue(corpus, out var artifact))
                s_artifacts[corpus] = artifact = Of(corpus).GenerateArtifact();
            return artifact.Split('\n');
        }
    }

    /// <summary>
    /// The cache guards of an artifact: its <c>cacheEntries</c> and <c>cacheTotal</c> lines (the
    /// pilot's count guard, <c>cachePilotCaseIds.length</c>, is not one of them).
    /// </summary>
    private static List<string> CacheGuardLines(string corpus)
        => ArtifactLines(corpus).Where(line => line.StartsWith("#guard cacheEntries ", StringComparison.Ordinal)
            || line.StartsWith("#guard cacheTotal ", StringComparison.Ordinal)).ToList();

    /// <summary>
    /// The reviewed pilot, case by case, with the EXACT cache guard lines its artifact carries
    /// (<c>|</c>-separated, hand-written): one line per listed name — a watched, unpublished name at
    /// zero — and one total line. The neutral guard of the case is the one the corpus already had.
    /// </summary>
    [Theory]
    // Semantic explorer (expectations observed from C#, reviewed in the generator's pilot table).
    [InlineData(Explorer, "special__listSpreadConcat", CachePilotCase.SuccessWithEntries, "ok raw=L[1, 2, 3, 4] n=1",
        "#guard cacheEntries case_special__listSpreadConcat \"A\" == some 1|#guard cacheEntries case_special__listSpreadConcat \"B\" == some 1|#guard cacheTotal case_special__listSpreadConcat == some 2")]
    [InlineData(Explorer, "root__p12", CachePilotCase.SuccessWithEmptyCache, "ok raw=S[1, 2] n=1",
        "#guard cacheTotal case_root__p12 == some 0")]
    [InlineData(Explorer, "indexBig__p12", CachePilotCase.FailureAfterPublication, "err index",
        "#guard cacheEntries case_indexBig__p12 \"x\" == some 1|#guard cacheTotal case_indexBig__p12 == some 1")]
    [InlineData(Explorer, "special__repeatedNameFailedThenValue", CachePilotCase.FailureBeforePublication, "err div0",
        "#guard cacheEntries case_special__repeatedNameFailedThenValue \"Bad\" == some 0|#guard cacheTotal case_special__repeatedNameFailedThenValue == some 0")]
    // Canonical language specification (hand-written expectations on the corpus cases).
    [InlineData(Spec, "property-value-boundary", CachePilotCase.SuccessWithEntries, "ok raw=S[S[10, 20], 10, 20, 997] n=4",
        "#guard cacheEntries case_property_value_boundary \"Coordinates\" == some 1|#guard cacheTotal case_property_value_boundary == some 1")]
    [InlineData(Spec, "expanded-map-calls-may-skip-indexed-arguments", CachePilotCase.SuccessWithEmptyCache, "ok raw=L[0, 0] n=1",
        "#guard cacheEntries case_expanded_map_calls_may_skip_indexed_arguments \"L\" == some 0|#guard cacheTotal case_expanded_map_calls_may_skip_indexed_arguments == some 0")]
    [InlineData(Spec, "index-out-of-range", CachePilotCase.FailureAfterPublication, "err index",
        "#guard cacheEntries case_index_out_of_range \"x\" == some 1|#guard cacheTotal case_index_out_of_range == some 1")]
    [InlineData(Spec, "if-spread-builds-values-before-branch-selection", CachePilotCase.FailureBeforePublication, "err div0",
        "#guard cacheEntries case_if_spread_builds_values_before_branch_selection \"Risky\" == some 0|#guard cacheTotal case_if_spread_builds_values_before_branch_selection == some 0")]
    // SEM-2C generated cases (identity-prelude base members; the alpha-rename member guards the total).
    [InlineData(Generated, "sem2b/v2/sys/cache/0", CachePilotCase.SuccessWithEntries, "ok raw=S[L[1, 1], 997] n=2",
        "#guard cacheEntries case_sem2b_2Fv2_2Fsys_2Fcache_2F0 \"v1\" == some 1|#guard cacheTotal case_sem2b_2Fv2_2Fsys_2Fcache_2F0 == some 1|#guard cacheTotal case_sem2b_2Fv2_2Fsys_2Fcache_2F0_alpha == some 1")]
    [InlineData(Generated, "sem2b/v2/sys/cache/2", CachePilotCase.SuccessWithEmptyCache, "ok raw=S[2, 997] n=2",
        "#guard cacheTotal case_sem2b_2Fv2_2Fsys_2Fcache_2F2 == some 0|#guard cacheTotal case_sem2b_2Fv2_2Fsys_2Fcache_2F2_alpha == some 0")]
    [InlineData(Generated, "sem2b/v2/sys/select-fail/3", CachePilotCase.FailureAfterPublication, "err index",
        "#guard cacheEntries case_sem2b_2Fv2_2Fsys_2Fselect_2Dfail_2F3 \"v1\" == some 1|#guard cacheTotal case_sem2b_2Fv2_2Fsys_2Fselect_2Dfail_2F3 == some 1|#guard cacheTotal case_sem2b_2Fv2_2Fsys_2Fselect_2Dfail_2F3_alpha == some 1")]
    [InlineData(Generated, "sem2b/v2/sys/cache-fail/0", CachePilotCase.FailureBeforePublication, "err div0",
        "#guard cacheEntries case_sem2b_2Fv2_2Fsys_2Fcache_2Dfail_2F0 \"v1\" == some 0|#guard cacheTotal case_sem2b_2Fv2_2Fsys_2Fcache_2Dfail_2F0 == some 0|#guard cacheTotal case_sem2b_2Fv2_2Fsys_2Fcache_2Dfail_2F0_alpha == some 0")]
    public void PilotCase_HasTheReviewedClassAndExactlyTheReviewedGuardLines(
        string corpus, string caseId, string expectedClass, string expectedNeutral, string expectedGuardLines)
    {
        var pilot = Of(corpus);
        var pilotCase = pilot.Cases.Single(c => c.CaseId == caseId);
        Assert.Equal(expectedClass, pilotCase.Class);
        Assert.Equal(expectedNeutral, pilotCase.Neutral);

        var (_, memberNames) = pilot.Program(caseId);
        var names = new HashSet<string>([pilotCase.LeanName, .. memberNames], StringComparer.Ordinal);
        var lines = ArtifactLines(corpus);
        Assert.Equal(expectedGuardLines.Split('|'), CacheGuardLines(corpus).Where(line => names.Contains(line.Split(' ')[2])));

        // The existing result oracle is untouched: the case keeps its ONE neutral guard.
        Assert.Single(lines, line => line == $"#guard obs {pilotCase.LeanName} == {LeanAstEncoder.QuoteString(expectedNeutral)}");
    }

    /// <summary>
    /// Each pilot covers the four classes once, and its artifact observes the cache of NO other
    /// program: every cache guard names a pilot definition (or a pilot case's transformation
    /// member), the pilot's count guard is present, and the partition comment states the three
    /// publication states over the artifact's programs.
    /// </summary>
    [Theory]
    [InlineData(Explorer)]
    [InlineData(Spec)]
    [InlineData(Generated)]
    public void Pilot_CoversTheFourClasses_AndNoOtherProgramHasACacheObservation(string corpus)
    {
        var pilot = Of(corpus);
        Assert.Equal(CachePilotCase.Classes.Order(StringComparer.Ordinal), pilot.Cases.Select(c => c.Class).Order(StringComparer.Ordinal));
        Assert.Equal(pilot.Cases.Count, pilot.Cases.Select(c => c.CaseId).Distinct(StringComparer.Ordinal).Count());

        var allowed = pilot.Cases
            .SelectMany(c => new[] { c.LeanName }.Concat(pilot.Program(c.CaseId).MemberLeanNames))
            .ToHashSet(StringComparer.Ordinal);
        var guards = CacheGuardLines(corpus);
        Assert.All(guards, line => Assert.Contains(line.Split(' ')[2], allowed));
        Assert.All(allowed, name => Assert.Single(guards, line => line.StartsWith($"#guard cacheTotal {name} == some ", StringComparison.Ordinal)));
        Assert.DoesNotContain(guards, line => line.Contains("== none", StringComparison.Ordinal));

        var lines = ArtifactLines(corpus);
        Assert.Single(lines, line => line == $"#guard cachePilotCaseIds.length == {pilot.Cases.Count}");

        // The three states over the artifact's base programs, by the reviewed expectation each has
        // (or lacks): entries, an empty cache, no observation. A pilot case's transformation members
        // are further programs, guarded on their total; every other member has no observation.
        var expectations = pilot.Cases.ToDictionary(c => c.CaseId, c => c.Expectation, StringComparer.Ordinal);
        var states = pilot.BaseProgramIds
            .Select(id => CachePublicationExpectation.StateOf(expectations.GetValueOrDefault(id)))
            .GroupBy(state => state).ToDictionary(g => g.Key, g => g.Count());
        Assert.Equal(2, states[CachePublicationState.CompletedNonEmpty]);
        Assert.Equal(2, states[CachePublicationState.CompletedEmpty]);
        Assert.Equal(pilot.BaseProgramIds.Count - pilot.Cases.Count, states[CachePublicationState.NotObserved]);
        Assert.True(states[CachePublicationState.NotObserved] > 0);

        var memberGuards = allowed.Count - pilot.Cases.Count;
        Assert.Contains(
            "- " + CachePilotCase.PartitionLine(pilot.Cases, pilot.BaseProgramIds.Count + pilot.MemberPrograms, memberGuards),
            string.Join('\n', lines), StringComparison.Ordinal);
    }

    /// <summary>
    /// C#-side sensitivity of every pilot case: the observer runs the program and REFUSES a
    /// reviewed expectation C# does not meet, naming the corpus and the case — whether the wrong
    /// expectation claims an empty cache, one entry too many, or an entry under a name the run never
    /// published. So no generated cache guard can pin an unreviewed or unmet number.
    /// </summary>
    [Theory]
    [InlineData(Explorer)]
    [InlineData(Spec)]
    [InlineData(Generated)]
    public void PilotCase_CacheObserverRejectsWrongReviewedExpectations(string corpus)
    {
        var pilot = Of(corpus);
        foreach (var pilotCase in pilot.Cases)
        {
            var (root, _) = pilot.Program(pilotCase.CaseId);
            var reviewed = pilotCase.Expectation;

            // The reviewed expectation itself is met.
            var observed = ZeroArgPublicationObserver.ObservePilotCase(pilot.CorpusLabel, pilotCase.CaseId, root, pilotCase.Neutral, reviewed);
            Assert.Equal(reviewed.Total, observed.Total);

            var entries = reviewed.Entries.ToArray();
            var wrong = new List<CachePublicationExpectation>
            {
                // An entry under a name the run never published.
                CachePublicationExpectation.Of([.. entries, ("NeverPublished", 1)]),
            };
            if (entries.Length > 0)
            {
                // One entry too many (or a publication claimed for the watched, unpublished name).
                wrong.Add(CachePublicationExpectation.Of([(entries[0].Name, entries[0].Count + 1), .. entries.Skip(1)]));
            }

            if (reviewed.Total > 0)
            {
                // Preserve every count and the total, but attribute a publication to the wrong name.
                // A total-only observer would accept this expectation.
                var published = Array.FindIndex(entries, entry => entry.Count > 0);
                var renamed = entries.ToArray();
                renamed[published] = ("NeverPublished", entries[published].Count);
                wrong.Add(CachePublicationExpectation.Of(renamed));

                // An empty cache claimed for a run that published, with and without watching the names.
                wrong.Add(CachePublicationExpectation.Nothing);
                wrong.Add(CachePublicationExpectation.Of(entries.Select(entry => (entry.Name, 0)).ToArray()));
            }

            foreach (var expectation in wrong)
            {
                var ex = Assert.Throws<InvalidOperationException>(() => ZeroArgPublicationObserver.ObservePilotCase(
                    pilot.CorpusLabel, pilotCase.CaseId, root, pilotCase.Neutral, expectation));
                Assert.Contains($"{pilot.CorpusLabel} route disagreement for '{pilotCase.CaseId}'", ex.Message, StringComparison.Ordinal);
                Assert.Contains("not the reviewed cache expectation", ex.Message, StringComparison.Ordinal);
            }

            // The cache observation belongs to the outcome the corpus guards: another neutral is refused.
            var otherNeutral = pilotCase.IsSuccess ? "err div0" : "ok raw=0 n=1";
            var mismatch = Assert.Throws<InvalidOperationException>(() => ZeroArgPublicationObserver.ObservePilotCase(
                pilot.CorpusLabel, pilotCase.CaseId, root, otherNeutral, reviewed));
            Assert.Contains("not the corpus observation", mismatch.Message, StringComparison.Ordinal);
        }
    }

    /// <summary>
    /// The three publication states are three different observations, and none is written like
    /// another: a missing observation is <c>none</c>, never <c>some 0</c>.
    /// </summary>
    [Fact]
    public void PublicationStates_NoObservationEmptyCacheAndEntriesAreNeverWrittenAlike()
    {
        var empty = new CachePublications(new Dictionary<string, int>(), 0);
        var entries = new CachePublications(new Dictionary<string, int> { ["A"] = 2 }, 2);

        // A completed observation is empty or not; NO observation is the absence of an expectation.
        Assert.Equal(CachePublicationState.CompletedEmpty, empty.State);
        Assert.Equal(CachePublicationState.CompletedNonEmpty, entries.State);
        Assert.Equal(CachePublicationState.NotObserved, CachePublicationExpectation.StateOf(null));
        Assert.Equal(CachePublicationState.CompletedEmpty, CachePublicationExpectation.StateOf(CachePublicationExpectation.Nothing));
        Assert.Equal(CachePublicationState.CompletedNonEmpty, CachePublicationExpectation.StateOf(CachePublicationExpectation.Parse("A=2")));
        Assert.Equal(3, Enum.GetValues<CachePublicationState>().Distinct().Count());

        // A reviewed expectation is always a completed run; "nothing published" and a watched name
        // at zero are both an EMPTY cache, and the absence of an expectation is the third state.
        Assert.Equal(CachePublicationState.CompletedEmpty, CachePublicationExpectation.Nothing.State);
        Assert.Equal(CachePublicationState.CompletedEmpty, CachePublicationExpectation.Parse("L=0").State);
        Assert.Equal(CachePublicationState.CompletedNonEmpty, CachePublicationExpectation.Parse("L=0 x=1").State);
        Assert.True(CachePublicationExpectation.Nothing.Matches(empty));
        Assert.True(CachePublicationExpectation.Parse("L=0").Matches(empty));
        Assert.False(CachePublicationExpectation.Nothing.Matches(entries));
        Assert.False(CachePublicationExpectation.Parse("A=1").Matches(entries));
        Assert.True(CachePublicationExpectation.Parse("A=2").Matches(entries));
        // An entry under an unlisted name is never absorbed by a matching total.
        Assert.False(CachePublicationExpectation.Parse("B=2").Matches(entries));

        Assert.Throws<FormatException>(() => CachePublicationExpectation.Parse("A"));
        Assert.Throws<FormatException>(() => CachePublicationExpectation.Parse("A=-1"));
        Assert.Throws<ArgumentException>(() => CachePublicationExpectation.Parse("A=1 A=1"));
    }

    /// <summary>
    /// The matched pair behind every pilot's two failing classes, on the shared C# observer itself:
    /// ONE program text with its two rows swapped. Reading <c>X</c> and then dividing by zero fails
    /// AFTER the publication and keeps the entry; dividing by zero first fails BEFORE it and
    /// completes with an empty cache. Both are completed observations of a failed run.
    /// </summary>
    [Theory]
    [InlineData("X = 7\nX\n1 / 0", "X=1")]
    [InlineData("X = 7\n1 / 0\nX", "X=0")]
    public void FailedRun_KeepsWhatWasPublishedBeforeTheFailure_AndNothingAfter(string source, string entries)
    {
        var root = SourceProvenance.ParseValid(source).Root;
        var published = ZeroArgPublicationObserver.ObserveSourceProgram("Observer control", source, root, "err div0");
        var expectation = CachePublicationExpectation.Parse(entries);
        Assert.True(expectation.Matches(published), $"published [{CachePublicationExpectation.Describe(published)}], expected [{expectation}]");

        var builder = new System.Text.StringBuilder();
        ZeroArgPublicationObserver.AppendCacheGuards(builder, "probe", ["X"], published);
        Assert.Equal($"#guard cacheEntries probe \"X\" == some {expectation.Total}\n#guard cacheTotal probe == some {expectation.Total}\n", builder.ToString());
    }
}
