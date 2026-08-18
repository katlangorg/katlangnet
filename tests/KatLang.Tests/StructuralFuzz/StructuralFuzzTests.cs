using System.Collections.Concurrent;
using System.Text.RegularExpressions;

namespace KatLang.Tests.StructuralFuzz;

/// <summary>
/// Conditional / pattern / scope-graph structural fuzzing: deterministic
/// metamorphic properties over generated programs with an explicit
/// generator-side scope graph.
///
/// <para><b>Oracles</b> (never derived from the implementation under test):</para>
/// <list type="number">
/// <item>METAMORPHIC — for each <see cref="StructuralRule"/> candidate, the
/// transformed program must relate to the original exactly as the rule's
/// semantic precondition proves (equivalence, known count delta, known error
/// class/phase).</item>
/// <item>ABSOLUTE MODEL ANCHORS — the generator KNOWS the selected branch /
/// matched clause by construction, so its sentinel atom must appear in the
/// neutral raw observation and the unselected sentinels must not. This is what
/// keeps the suite from being blind to defects that break BOTH sides of a
/// metamorphic pair identically (e.g. reversed clause dispatch).</item>
/// <item>Every observation goes through <see cref="SemanticExplorerHarness"/>,
/// which already cross-checks Evaluator.RunCounted, Evaluator.Run and
/// KatLangEngine.Run on every case — so all three entry points participate
/// without tripling the corpus.</item>
/// </list>
///
/// <para><b>Lean.</b> The generated subset (properties, braces, flat and
/// clause-family calls, sequence patterns, deconstruction, if, spread/capture)
/// is inside the Lean-modelled surface whose C#/Lean agreement is pinned by
/// the generated SemanticExplorerCases corpus; this campaign adds no live
/// per-case Lean execution (lake builds per generated case would not be CI
/// viable) and instead relies on those standing differential guards plus the
/// metamorphic/anchor oracles here. Representability is reported by the
/// health fact.</para>
/// </summary>
public class StructuralFuzzTests
{
    private static readonly IReadOnlyList<GeneratedCase> Corpus = StructuralCorpus.All();

    private static readonly IReadOnlyDictionary<string, GeneratedCase> ById =
        Corpus.ToDictionary(c => c.CaseId, StringComparer.Ordinal);

    private static readonly ConcurrentDictionary<string, ExplorerObservation> OriginalCache = new();

    /// <summary>Candidates evaluated per (rule, base case): bounds suite cost
    /// while every rule still ranges over the whole corpus.</summary>
    private const int CandidatesPerRulePerCase = 2;

    /// <summary>Checked-in regression seeds for real discovered bugs. Every
    /// entry must keep reproducing (meta-test); the campaign found none, so
    /// the list is empty — mutation-kill reproducers live in the report, not
    /// here, because the mutations were reverted.</summary>
    public static IReadOnlyList<(string Name, string CaseId, StructuralRule Rule)> RegressionSeeds { get; } = [];

    public static TheoryData<string> RuleNames()
    {
        var data = new TheoryData<string>();
        foreach (var rule in Enum.GetValues<StructuralRule>())
            data.Add(rule.ToString());
        return data;
    }

    // ── The metamorphic property, one theory per rule ───────────────────────

    [Theory]
    [MemberData(nameof(RuleNames))]
    public void EveryCandidateOfRule_SatisfiesItsExpectedRelation(string ruleName)
    {
        var rule = Enum.Parse<StructuralRule>(ruleName);
        var exercised = 0;

        foreach (var baseCase in Corpus)
        {
            var candidates = StructuralTransforms.Enumerate(baseCase.Program)
                .Where(c => c.Rule == rule)
                .Take(CandidatesPerRulePerCase)
                .ToList();
            if (candidates.Count == 0)
                continue;

            var original = ObserveOriginal(baseCase);
            foreach (var candidate in candidates)
            {
                exercised++;
                if (Violation(original, candidate) is { } violation)
                    FailWithReport(baseCase, original, candidate, violation);
            }
        }

        Assert.True(exercised > 0, $"Rule {rule} produced no candidates anywhere in the corpus — dead rule family.");
    }

    /// <summary>Observes (and caches) a base case, enforcing valid-mode power:
    /// the original program must parse and evaluate, and must satisfy its
    /// model-derived sentinel anchors.</summary>
    private static ExplorerObservation ObserveOriginal(GeneratedCase baseCase)
        => OriginalCache.GetOrAdd(baseCase.CaseId, _ =>
        {
            var source = baseCase.Program.Render();
            var observation = SemanticExplorerHarness.Observe(baseCase.CaseId, source);
            if (observation.Outcome != "ok")
            {
                Assert.Fail(
                    $"GENERATOR BUG (not an implementation finding): valid-mode base case {baseCase.CaseId} did not "
                    + $"evaluate — outcome {observation.Outcome} {observation.ErrorCategory}.\nSource:\n{source}\n"
                    + $"Scope model:\n{baseCase.Program.DescribeScopes()}");
            }

            AssertAnchors(baseCase, observation);
            return observation;
        });

    private static void AssertAnchors(GeneratedCase baseCase, ExplorerObservation observation)
    {
        var tokens = AtomTokens(observation.Raw!);
        foreach (var expected in baseCase.Program.MustContainAtoms)
        {
            Assert.True(
                tokens.Contains(Token(expected)),
                $"[{baseCase.CaseId}] ABSOLUTE ANCHOR violated: the generator-selected branch/clause sentinel {expected} "
                + $"is missing from the observation — the wrong branch or clause was chosen.\n"
                + $"raw: {observation.Raw}\nSource:\n{baseCase.Program.Render()}");
        }

        foreach (var forbidden in baseCase.Program.MustNotContainAtoms)
        {
            Assert.True(
                !tokens.Contains(Token(forbidden)),
                $"[{baseCase.CaseId}] ABSOLUTE ANCHOR violated: sentinel {forbidden} of an UNSELECTED branch/clause "
                + $"appeared in the observation.\nraw: {observation.Raw}\nSource:\n{baseCase.Program.Render()}");
        }
    }

    private static string Token(decimal value) => value.ToString(System.Globalization.CultureInfo.InvariantCulture);

    private static IReadOnlySet<string> AtomTokens(string raw)
        => Regex.Matches(raw, @"\d+(\.\d+)?").Select(m => m.Value).ToHashSet(StringComparer.Ordinal);

    /// <summary>Rule-specific relation check; returns a violation description
    /// or null. Normalization is rule-specific by construction: equivalence
    /// compares the exact neutral raw + count + display; delta rules compare
    /// exact raw and the exact expected count; error rules compare outcome
    /// class and category only.</summary>
    private static string? Violation(ExplorerObservation original, TransformCandidate candidate)
    {
        if (candidate.ValidateTransformedNaming)
            candidate.Transformed.ValidateNaming();

        var transformed = SemanticExplorerHarness.Observe("transformed", candidate.Transformed.Render());
        switch (candidate.Relation)
        {
            case ExpectedRelation.Equivalent:
                if (transformed.Outcome != original.Outcome)
                    return $"outcome changed: {original.Outcome} → {transformed.Outcome} {transformed.ErrorCategory}";
                if (transformed.Neutral != original.Neutral)
                    return $"neutral observation changed:\n  original:    {original.Neutral}\n  transformed: {transformed.Neutral}";
                if (transformed.Display != original.Display)
                    return $"display changed:\n  original:    {original.Display}\n  transformed: {transformed.Display}";
                return null;

            case ExpectedRelation.RawPreservedCountBecomes delta:
                if (original.Emitted == delta.NewCount)
                    return $"POWER violation: the delta case is degenerate — original count already {delta.NewCount}";
                if (transformed.Outcome != "ok")
                    return $"expected ok with count {delta.NewCount} but got {transformed.Outcome} {transformed.ErrorCategory}";
                if (transformed.Raw != original.Raw)
                    return $"raw structure changed:\n  original:    {original.Raw}\n  transformed: {transformed.Raw}";
                if (transformed.Emitted != delta.NewCount)
                    return $"emitted count: expected {delta.NewCount}, observed {transformed.Emitted} (original {original.Emitted})";
                return null;

            case ExpectedRelation.BecomesRuntimeError error:
                if (transformed.Outcome != "err")
                    return $"expected err {error.Category} but got outcome {transformed.Outcome}";
                if (transformed.ErrorCategory != error.Category)
                    return $"expected err {error.Category} but got err {transformed.ErrorCategory}";
                return null;

            case ExpectedRelation.BecomesFrontEndError:
                return transformed.Outcome == "parseError"
                    ? null
                    : $"expected a front-end rejection but got outcome {transformed.Outcome}";

            default:
                throw new InvalidOperationException($"Unhandled relation {candidate.Relation.GetType().Name}");
        }
    }

    private static void FailWithReport(
        GeneratedCase baseCase,
        ExplorerObservation original,
        TransformCandidate candidate,
        string violation)
    {
        var shrunk = StructuralShrinker.Shrink(
            baseCase.Program,
            candidate.Rule,
            (program, reducedCandidate) =>
            {
                var reducedOriginal = SemanticExplorerHarness.Observe("shrink-base", program.Render());
                return reducedOriginal.Outcome == "ok" && Violation(reducedOriginal, reducedCandidate) is not null;
            });

        Assert.Fail(
            $"""
            Structural fuzz failure
            Rule: {candidate.Rule}
            Case: {baseCase.CaseId}
            Invariant: {candidate.Description}
            Expected relation: {candidate.Relation}
            Violation: {violation}

            Original:
            {baseCase.Program.Render()}

            Transformed:
            {candidate.Transformed.Render()}

            Original observation: {original.Neutral}
            Scope model:
            {baseCase.Program.DescribeScopes()}
            Shrunk reproducer ({shrunk.OriginalSize} → {shrunk.ShrunkSize} nodes, {shrunk.AcceptedReductions} reductions):
            {shrunk.Program.Render()}
            Shrunk transformed:
            {shrunk.FailingCandidate.Transformed.Render()}
            """);
    }

    // ── Absolute anchors on every base case ─────────────────────────────────

    /// <summary>Runs every base case once: valid-mode success + sentinel
    /// anchors. This is the absolute channel that kills mutations breaking
    /// both sides of a metamorphic pair identically.</summary>
    [Fact]
    public void EveryBaseCase_EvaluatesAndSatisfiesItsModelAnchors()
    {
        foreach (var baseCase in Corpus)
            ObserveOriginal(baseCase);
    }

    // ── Meta / integrity ────────────────────────────────────────────────────

    [Fact]
    public void CaseIds_AreUnique()
        => Assert.Equal(Corpus.Count, Corpus.Select(c => c.CaseId).Distinct(StringComparer.Ordinal).Count());

    [Fact]
    public void CorpusEnumeration_IsDeterministic()
    {
        var again = StructuralCorpus.All();
        Assert.Equal(Corpus.Count, again.Count);
        foreach (var (a, b) in Corpus.Zip(again))
        {
            Assert.Equal(a.CaseId, b.CaseId);
            Assert.Equal(a.Program.Render(), b.Program.Render());
        }
    }

    /// <summary>No rule family may silently die: every StructuralRule must have
    /// candidates in the deterministic corpus (counted without evaluating).</summary>
    [Fact]
    public void EveryRule_HasCandidatesInTheCorpus()
    {
        var counts = Enum.GetValues<StructuralRule>().ToDictionary(r => r, _ => 0);
        foreach (var baseCase in Corpus)
        {
            foreach (var candidate in StructuralTransforms.Enumerate(baseCase.Program))
                counts[candidate.Rule]++;
        }

        foreach (var (rule, count) in counts)
            Assert.True(count > 0, $"Rule {rule} has no candidates in the corpus — the family silently disappeared.");
    }

    /// <summary>Required pairwise interactions among the major structural
    /// dimensions must actually be generated.</summary>
    [Fact]
    public void RequiredPairwiseInteractions_ArePresent()
    {
        (string A, string B)[] required =
        [
            ("if", "shadow"),
            ("if", "brace"),
            ("family", "shadow"),
            ("family", "if"),
            ("family", "catchAll"),
            ("collecting", "spread"),
            ("deconstruct", "collecting"),
            ("deconstruct", "brace"),
            ("shadow", "multiOut"),
            ("seqPattern", "collecting"),
            ("zeroOut", "shadow"),
            ("userCall", "shadow"),
            ("multiOut", "spread"),
        ];

        foreach (var (a, b) in required)
        {
            Assert.True(
                Corpus.Any(c => c.Features.Contains(a) && c.Features.Contains(b)),
                $"Required pairwise interaction ({a} × {b}) has no generated case.");
        }
    }

    /// <summary>Generator health: tier sizes, per-rule candidate distribution,
    /// and structural statistics — broad invariants, not fragile percentages.
    /// Enumeration only; nothing is evaluated here.</summary>
    [Fact]
    public void GeneratorHealth_TiersRulesAndDepthsAreAlive()
    {
        var exhaustive = StructuralCorpus.ExhaustiveCases();
        var seeded = StructuralCorpus.SeededCases();
        Assert.True(exhaustive.Count >= 60, $"exhaustive tier shrank to {exhaustive.Count}");
        Assert.True(seeded.Count >= 60, $"seeded tier shrank to {seeded.Count}");

        var candidateCount = 0;
        var equivalence = 0;
        var delta = 0;
        var runtimeError = 0;
        var frontEndError = 0;
        var maxSize = 0;
        foreach (var baseCase in Corpus)
        {
            maxSize = Math.Max(maxSize, StructuralShrinker.Size(baseCase.Program));
            foreach (var candidate in StructuralTransforms.Enumerate(baseCase.Program))
            {
                candidateCount++;
                switch (candidate.Relation)
                {
                    case ExpectedRelation.Equivalent: equivalence++; break;
                    case ExpectedRelation.RawPreservedCountBecomes: delta++; break;
                    case ExpectedRelation.BecomesRuntimeError: runtimeError++; break;
                    case ExpectedRelation.BecomesFrontEndError: frontEndError++; break;
                }
            }
        }

        Assert.True(candidateCount > 500, $"total candidate volume collapsed: {candidateCount}");
        Assert.True(equivalence > runtimeError + frontEndError,
            "equivalence properties must dominate the error-metamorphism families");
        Assert.True(delta > 0 && runtimeError > 0 && frontEndError > 0, "a relation family died");
        Assert.True(maxSize is > 10 and < 400, $"generated size out of expected envelope: {maxSize}");
    }

    /// <summary>Shrinker mechanics on a fixture: with an always-violating
    /// oracle, minimization must strictly reduce a large case while keeping
    /// the rule applicable and the naming valid — i.e. it preserves rule
    /// preconditions while shrinking.</summary>
    [Fact]
    public void Shrinker_ReducesWhilePreservingRulePreconditions()
    {
        var big = Corpus.First(c => c.CaseId.StartsWith("seed/", StringComparison.Ordinal)
            && StructuralTransforms.Enumerate(c.Program).Any(t => t.Rule == StructuralRule.AlphaRenameLocal));

        var result = StructuralShrinker.Shrink(
            big.Program,
            StructuralRule.AlphaRenameLocal,
            (_, _) => true);

        Assert.True(result.ShrunkSize < result.OriginalSize,
            $"shrinker made no progress ({result.OriginalSize} → {result.ShrunkSize})");
        result.Program.ValidateNaming();
        Assert.Contains(
            StructuralTransforms.Enumerate(result.Program),
            c => c.Rule == StructuralRule.AlphaRenameLocal);
    }

    /// <summary>Every checked-in regression seed must keep reproducing its
    /// original relation (currently empty: the campaign found no
    /// implementation defect, so there is nothing to pin here).</summary>
    [Fact]
    public void RegressionSeeds_AllReproduce()
    {
        foreach (var (name, caseId, rule) in RegressionSeeds)
        {
            var baseCase = ById[caseId];
            var original = ObserveOriginal(baseCase);
            var candidates = StructuralTransforms.Enumerate(baseCase.Program).Where(c => c.Rule == rule).ToList();
            Assert.True(candidates.Count > 0, $"regression '{name}': rule {rule} no longer applies to {caseId}");
            foreach (var candidate in candidates)
                Assert.True(Violation(original, candidate) is null, $"regression '{name}' violated again");
        }
    }
}
