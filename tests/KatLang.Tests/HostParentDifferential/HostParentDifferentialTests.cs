using System.Globalization;
using System.Text;
using System.Text.RegularExpressions;

namespace KatLang.Tests;

/// <summary>
/// HOST-DIFF-1: generates and pins <c>lean/CoreTests/HostParentDifferential.lean</c>, the Lean/C#
/// differential corpus of HOST-BUILT ASTs with pre-wired <see cref="ScopeCtx"/> parent chains
/// (<see cref="HostParentDifferentialCorpus"/>). For every case the ONE constructed program graph is
/// evaluated by C# on every route (<see cref="HostParentDifferentialHarness"/>) and encoded for Lean
/// by <see cref="LeanAstEncoder"/>; the artifact guards Lean's neutral observation and published
/// zero-argument cache entries against the recorded C# ones, and <c>lake build CoreTests</c>
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

    /// <summary>Stable, unique ids; every HP-01..HP-14 family of the HOST-DIFF-1 matrix is present, plus DECON-CACHE-2's HP-15.</summary>
    [Fact]
    public void CorpusIds_AreStableUnique_AndCoverTheWholeMatrix()
    {
        var cases = HostParentDifferentialCorpus.AllCases();
        Assert.All(cases, c => Assert.Matches("^HP-[0-9]{2}[a-z]$", c.Id));
        Assert.Equal(cases.Count, cases.Select(c => c.Id).Distinct(StringComparer.Ordinal).Count());
        Assert.Equal(cases.Count, cases.Select(c => c.LeanName).Distinct(StringComparer.Ordinal).Count());
        var families = cases.Select(c => c.Id[..5]).Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToList();
        Assert.Equal(Enumerable.Range(1, 15).Select(n => $"HP-{n:00}"), families);
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
    /// Coverage ratchet: the pinned minimums may only be RAISED (or lowered in a reviewed diff that
    /// deliberately removes cases). An encoder regression cannot pass silently — a case that stops
    /// encoding fails generation loudly — and a case moved to the divergent partition breaks the
    /// exact id list above.
    /// </summary>
    [Fact]
    public void FidelityRatchet_ComparableHostParentCoverageCannotSilentlyShrink()
    {
        const int MinimumComparableCases = 102;
        const int MinimumComparableCasesWithPreWiredParents = 96;
        const int MinimumCacheGuards = 181;

        var cases = HostParentDifferentialCorpus.AllCases();
        var comparable = cases.Where(c => c.Divergence is null).ToList();
        var wired = comparable.Count(c => LeanAstEncoder.EncodeExpr(c.Program).Contains("Algorithm.withParent (some ", StringComparison.Ordinal));
        var cacheGuards = comparable.Select(c => (Case: c, Observation: HostParentDifferentialHarness.Observe(c)))
            .Where(pair => pair.Observation.IsSuccess)
            .Sum(pair => WatchedNames(pair.Case, pair.Observation).Count);

        Assert.True(comparable.Count >= MinimumComparableCases,
            $"Comparable host-parent differential coverage shrank below {MinimumComparableCases} (actual {comparable.Count}).");
        Assert.True(wired >= MinimumComparableCasesWithPreWiredParents,
            $"Comparable cases with an encoded pre-wired parent shrank below {MinimumComparableCasesWithPreWiredParents} (actual {wired}).");
        Assert.True(cacheGuards >= MinimumCacheGuards,
            $"Per-property cache guards shrank below {MinimumCacheGuards} (actual {cacheGuards}).");
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

    private static List<string> WatchedNames(HostParentCase hostCase, HostParentObservation observation)
        => hostCase.WatchedProperties.Concat(observation.PublishedByName.Keys).Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal).ToList();

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

            /-!
            GENERATED FILE - DO NOT EDIT BY HAND.

            HOST-DIFF-1: Lean/C# differential corpus of HOST-BUILT ASTs with pre-wired `ScopeCtx`
            parent chains (tests/KatLang.Tests/HostParentDifferential/HostParentDifferentialCorpus.cs).
            Each program below is `LeanAstEncoder`'s encoding of the SAME constructed C# AST the C#
            evaluator ran on every route (plain, counted, generic, optimized, suspending async); each
            `#guard` pins the C# neutral observation and the C# published zero-argument cache entries
            (per property name, and in total). A failing guard is a Lean/C# divergence on that case.

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
        builder.Append("""
            /-- Published zero-argument property cache entries of one run named `name` (C#: the entries the
                run-scoped publication law PUBLISHED for bindings of that name). -/
            def cacheEntries (e : Expr) (name : String) : Nat :=
              match runResultWithState e with
              | .ok (_, state) => (state.zeroArgPropertyCache.filter (·.1.propertyName == name)).length
              | .error _ => 0

            /-- Every published zero-argument property cache entry of one run. -/
            def cacheTotal (e : Expr) : Nat :=
              match runResultWithState e with
              | .ok (_, state) => state.zeroArgPropertyCache.length
              | .error _ => 0


            """.ReplaceLineEndings("\n"));

        var comparableIds = new List<string>();
        var divergentIds = new List<string>();
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
            LeanObsTemplate.AppendErrorGuard(builder, hostCase.LeanName, observation.ErrorPayload);
            if (observation.IsSuccess)
            {
                foreach (var name in WatchedNames(hostCase, observation))
                {
                    builder.Append($"#guard cacheEntries {hostCase.LeanName} {LeanAstEncoder.QuoteString(name)} == " +
                        $"{observation.Published(name).ToString(CultureInfo.InvariantCulture)}\n");
                }

                builder.Append($"#guard cacheTotal {hostCase.LeanName} == {observation.PublishedTotal.ToString(CultureInfo.InvariantCulture)}\n");
            }

            builder.Append('\n');
            comparableIds.Add(hostCase.Id);
        }

        SemanticExplorerLeanArtifactTests.AppendCountGuard(builder, "comparableCaseIds", comparableIds, comparableExpected,
            "Machine-checked comparable partition count: the id list is built by the loop that emits the guards\n" +
            "above, while the expected total is computed independently from the corpus partition.");
        SemanticExplorerLeanArtifactTests.AppendCountGuard(builder, "divergentCaseIds", divergentIds, divergentExpected,
            "Machine-checked known-divergence partition count (HOST-LEAN-O6 shapes pinned on both sides).");
        builder.Append($"-- {comparableIds.Count} comparable cases, {divergentIds.Count} known divergences.\n");
        builder.Append("end HostParentDifferential\n");
        return builder.ToString();
    }
}
