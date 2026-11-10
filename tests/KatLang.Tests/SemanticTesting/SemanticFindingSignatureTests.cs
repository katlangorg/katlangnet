using System.Text.Json.Nodes;
using KatLang.ParserFuzz;

namespace KatLang.Tests.SemanticTesting;

/// <summary>
/// SEM-2C structured findings (fuzz/README.md § Reduction): every runner finding carries a
/// structured record beside its text, the reduction signature is classified from that record, the
/// record survives the worker result document, and the text classifier remains only as the fallback
/// for documents that predate the records. Faults are injected through the runner's inert
/// observation seam or by editing a case's members, so every finding site is reached.
/// </summary>
public class SemanticFindingSignatureTests
{
    private static SemanticCase Find(Func<SemanticCase, bool> predicate) => SemanticGrammarCorpusTests.Cases.First(predicate);

    private static SemanticCase Success => Find(c => c.Kind == SemanticCaseKind.ValidSuccess && c.Members.Length == 3);

    private static SemanticCase RuntimeFailure => Find(c => c.Kind == SemanticCaseKind.ValidRuntimeFailure);

    private static SemanticCase Cancelling => Find(c => c.Paths.HasFlag(SemanticPath.Cancellation));

    private static SemanticCase OptimizedLoop => Find(c => c.Kind == SemanticCaseKind.ValidSuccess && c.Paths.HasFlag(SemanticPath.OptimizedLoop));

    private static SemanticCase Invalid(string phase) => Find(c => c.Kind == SemanticCaseKind.InvalidFrontEnd && c.Expected.DiagnosticPhase == phase);

    private static Func<SemanticProfileRun, SemanticProfileRun> On(string? profile, string member, Func<SemanticProfileRun, SemanticProfileRun> change)
        => run => (profile is null || run.Profile == profile) && run.Member == member ? change(run) : run;

    private static Func<SemanticProfileRun, SemanticProfileRun> OnObservation(string? profile, string member,
        Func<MetamorphicOperationalObservation, MetamorphicOperationalObservation> change)
        => On(profile, member, run => run.Observation is { } o ? run with { Observation = change(o) } : run);

    private static SemanticCase WithSources(SemanticCase semanticCase, string source)
        => semanticCase with { Members = [.. semanticCase.Members.Select(m => m with { Source = source })] };

    private const string Base = SemanticMember.BaseRole;

    /// <summary>One injected fault per finding site (several sites fire per scenario; all are checked).</summary>
    private static IEnumerable<(string Name, SemanticCaseResult Result)> Scenarios()
    {
        var success = Success;
        var optimized = SemanticProfiles.SyncOptimized;
        var generic = SemanticProfiles.SyncGeneric;
        (string, SemanticCaseResult) Run(string name, SemanticCase c, Func<SemanticProfileRun, SemanticProfileRun>? filter = null)
            => (name, SemanticRunner.Run(c, filter));

        yield return Run("value", success, OnObservation(optimized, Base, o => o with { Semantic = MetamorphicSemanticObservation.OfValue(new Result.Atom(123456), o.Semantic.EmittedCount) }));
        yield return Run("emitted-count", success, OnObservation(generic, Base, o => o with { Semantic = o.Semantic with { EmittedCount = o.Semantic.EmittedCount + 1 } }));
        yield return Run("emitted-count-missing", success, OnObservation(generic, Base, o => o with { Semantic = o.Semantic with { EmittedCount = null } }));
        yield return Run("structure-missing", success, OnObservation(optimized, Base, o => o with { Semantic = o.Semantic with { Value = null, StructuralIdentity = null } }));
        yield return Run("relation-observation-missing", success, OnObservation(optimized, SemanticMember.AlphaRenameRole, o => o with { Semantic = o.Semantic with { Value = null, StructuralIdentity = null } }));
        yield return Run("host-events", success, On(generic, Base, r => r with { Events = [.. r.Events, "trace:4242"] }));
        yield return Run("harness", success, On(generic, Base, r => r with { HarnessProblem = "injected harness problem" }));
        yield return Run("observation-missing", success, On(generic, Base, r => r with { Observation = null }));
        yield return Run("facet-contract", success, OnObservation(generic, Base, o => o with { Surface = "injected-surface" }));
        yield return Run("unscheduled-cancellation", success, On(generic, Base, r => r with { Cancelled = true }));
        yield return Run("surface-refused", success, On(generic, Base, r => r with { Ran = false, Reason = "injected", Observation = null }));
        yield return Run("resource-limit", success, OnObservation(generic, Base, o => o with { Semantic = MetamorphicSemanticObservation.Failure("injected-limit", null, isResourceLimit: true) }));
        yield return Run("outcome-success", success, OnObservation(generic, Base, o => o with { Semantic = MetamorphicSemanticObservation.Failure("injected", null, isResourceLimit: false) }));
        yield return Run("relation", success, OnObservation(optimized, SemanticMember.DeclarationReorderRole, o => o with { Semantic = MetamorphicSemanticObservation.OfValue(new Result.Atom(777), o.Semantic.EmittedCount) }));
        yield return Run("parity-counter", success, OnObservation(optimized, Base, o => o with { EvaluationSteps = o.EvaluationSteps + 1 }));

        yield return Run("path-evidence", OptimizedLoop, OnObservation(generic, Base, o => o with { OptimizerEvidence = null }));
        yield return Run("path-not-observed", OptimizedLoop, On(optimized, Base, r => r with { Observation = null }));

        var failure = RuntimeFailure;
        yield return Run("error-kind", failure, OnObservation(null, Base, o => o with { Semantic = o.Semantic with { ErrorCategory = "injected-kind" } }));
        yield return Run("error-missing", failure, OnObservation(null, Base, o => o with { Semantic = o.Semantic with { ErrorDetail = null } }));
        yield return Run("failure-stage", failure, OnObservation(null, Base, o => o with { FailureStage = MetamorphicOperationalObservation.FrontEndFailureStage }));
        yield return Run("outcome-failure", failure, OnObservation(null, Base, o => o with { Semantic = MetamorphicSemanticObservation.OfValue(new Result.Atom(1), 1) }));

        var cancelling = Cancelling;
        yield return Run("cancellation", cancelling, On(SemanticProfiles.AsyncTwinCancel, Base, r => r with { Cancelled = false }));
        yield return Run("cancellation-events", cancelling, On(SemanticProfiles.EngineRunAsyncCancel, Base, r => r with { Events = [.. r.Events, "trace:4242"] }));

        var syntax = Invalid(SemanticExpectation.SyntaxPhase);
        var elaboration = Invalid(SemanticExpectation.ElaborationPhase);
        yield return Run("front-end-reached", syntax, On(null, Base, r => r with { Reason = "injected" }));
        yield return Run("front-end-failure", syntax, OnObservation(null, Base, o => o with { FailureStage = MetamorphicOperationalObservation.EvaluationFailureStage }));
        yield return Run("front-end-effects", syntax, On(null, Base, r => r with { Events = ["trace:1"] }));
        yield return Run("front-end-accepted", WithSources(syntax, "1"));
        yield return Run("front-end-phase", WithSources(syntax, elaboration.Source));
        var otherSyntax = SemanticGrammarCorpusTests.Cases.First(c => c.Kind == SemanticCaseKind.InvalidFrontEnd
            && c.Expected.DiagnosticPhase == SemanticExpectation.SyntaxPhase && c.Expected.Diagnostic != syntax.Expected.Diagnostic);
        yield return Run("front-end-diagnostic", WithSources(syntax, otherSyntax.Source));
        yield return Run("front-end-rejected", success with { Members = success.Members.SetItem(0, success.Members[0] with { Source = "1 +" }) });

        yield return Run("case-contract", success with { Profiles = [] });
    }

    private static readonly Lazy<List<(string Name, SemanticCaseResult Result)>> AllScenarios = new(() => [.. Scenarios()]);

    /// <summary>
    /// Every finding the runner produces has an aligned record, and for every template the runner
    /// produces today the record classifies EXACTLY as the text did. So a structured signature equals
    /// the one a <c>kl-sem2b-reduction</c> v1 record stored, and old records keep their meaning.
    /// Every facet of the stable enumeration is reached.
    /// </summary>
    [Fact]
    public void EveryFindingHasARecord_ThatClassifiesExactlyAsItsText()
    {
        var reached = new HashSet<SemanticFindingFacet>();
        var findings = 0;
        foreach (var (name, result) in AllScenarios.Value)
        {
            Assert.False(result.Passed, $"{name}: the injected fault produced no finding");
            Assert.True(SemanticFailureSignature.HasAlignedRecords(result), $"{name}: findings without aligned records");
            for (var i = 0; i < result.Findings.Length; i++)
            {
                var record = result.FindingRecords[i];
                Assert.Equal(SemanticFailureSignature.ClassifyText(result.Findings[i]), SemanticFailureSignature.Classify(record));
                reached.Add(record.Facet);
                findings++;
            }
        }

        var missing = SemanticFindingFacets.All.Where(f => !reached.Contains(f)).ToList();
        Assert.True(missing.Count == 0, "facets never produced by a scenario: " + string.Join(", ", missing));
        Assert.True(findings > 40, $"only {findings} findings checked");
    }

    /// <summary>The verdict a record carries is the one its finding contributed to the case verdict.</summary>
    [Fact]
    public void RecordVerdicts_AggregateToTheCaseVerdict()
    {
        foreach (var (name, result) in AllScenarios.Value)
            Assert.True(result.FindingRecords.Any(r => r.Verdict == result.Verdict), $"{name}: no record carries the case verdict {result.Verdict}");
    }

    /// <summary>
    /// Rewording every finding leaves the signature unchanged, because it is classified from the
    /// record. The same reworded text WITHOUT records (the fallback) loses the facet: the premise
    /// that the text classifier alone would have been broken by the rewording.
    /// </summary>
    [Fact]
    public void RewordingAFinding_DoesNotChangeItsClassification()
    {
        var unchangedByFallback = new List<string>();
        foreach (var (name, result) in AllScenarios.Value)
        {
            var reworded = result with { Findings = [.. result.Findings.Select((f, i) => $"finding {i}, reworded: {new string(f.Reverse().ToArray())}")] };
            Assert.Equal(SemanticFailureSignature.Of(result), SemanticFailureSignature.Of(reworded));
            var fallback = reworded with { FindingRecords = [] };
            if (SemanticFailureSignature.Of(fallback) == SemanticFailureSignature.Of(result)) unchangedByFallback.Add(name);
        }

        // Only the case-contract finding has no location or facet text to lose (its fallback is "case" too).
        Assert.Equal(["case-contract"], unchangedByFallback);
    }

    /// <summary>A result without aligned records (an old worker document, or a hand-built result) uses the text classifier.</summary>
    [Fact]
    public void WithoutAlignedRecords_TheTextClassifierIsTheFallback()
    {
        var (_, result) = AllScenarios.Value.First(s => s.Name == "value");
        var text = result with { FindingRecords = [] };
        Assert.Equal(SemanticFailureSignature.Of(result), SemanticFailureSignature.Of(text));
        Assert.Equal(new SemanticFailureSignature(SemanticVerdict.Mismatch, Base, SemanticProfiles.SyncOptimized, "value"), SemanticFailureSignature.Of(text));

        // Misaligned records are never trusted: with one record too few, the (reworded) text decides.
        var misaligned = result with { FindingRecords = result.FindingRecords.RemoveAt(0), Findings = [.. result.Findings.Select(f => "reworded: " + f)] };
        Assert.False(SemanticFailureSignature.HasAlignedRecords(misaligned));
        Assert.Equal(new SemanticFailureSignature(SemanticVerdict.Mismatch, "-", "-", "case"), SemanticFailureSignature.Of(misaligned));
    }

    /// <summary>
    /// The worker result document carries the records (so a supervised reduction classifies from
    /// them); a document without them still parses and falls back; malformed records are refused.
    /// The case descriptor's recorded result keeps its v1 text exactly.
    /// </summary>
    [Fact]
    public void TheWorkerResultDocument_CarriesTheRecords_AndOlderDocumentsStillRead()
    {
        var checkedDocuments = 0;
        foreach (var (name, result) in AllScenarios.Value.Where(s => s.Result.Runs.Length > 0))
        {
            var document = SemanticDescriptor.WriteResultDocument(result);
            // Some injected observations (no emitted count, no value) are refused by the reader's
            // pre-existing observation checks; that refusal is independent of the records.
            var withoutRecords = JsonNode.Parse(document)!;
            withoutRecords["result"]!.AsObject().Remove("findingRecords");
            if (!SemanticDescriptor.TryParseResult(withoutRecords.ToJsonString(), out _, out _)) continue;
            checkedDocuments++;
            Assert.True(SemanticDescriptor.TryParseResult(document, out var summary, out var problem), $"{name}: {problem}");
            Assert.Equal(result.FindingRecords.ToArray(), summary.CoverageResult.FindingRecords.ToArray());
            Assert.Equal(SemanticFailureSignature.Of(result), SemanticFailureSignature.Of(summary.CoverageResult));

            // A document written before the records existed: the same document minus the member.
            var old = JsonNode.Parse(document)!;
            old["result"]!.AsObject().Remove("findingRecords");
            Assert.True(SemanticDescriptor.TryParseResult(old.ToJsonString(), out var oldSummary, out problem), $"{name}: {problem}");
            Assert.True(oldSummary.CoverageResult.FindingRecords.IsEmpty);
            Assert.Equal(SemanticFailureSignature.Of(result), SemanticFailureSignature.Of(oldSummary.CoverageResult));
        }

        Assert.True(checkedDocuments >= 20, $"only {checkedDocuments} result documents checked");

        var (_, value) = AllScenarios.Value.First(s => s.Name == "value");
        var text = SemanticDescriptor.WriteResultDocument(value);
        foreach (var (path, replacement) in new (string, JsonNode?)[]
        {
            ("facet", "no-such-facet"),
            ("verdict", "Passed"),
            ("verdict", "Sideways"),
            ("member", null),
            ("location", 7),
        })
        {
            var node = JsonNode.Parse(text)!;
            node["result"]!["findingRecords"]![0]![path] = replacement;
            Assert.False(SemanticDescriptor.TryParseResult(node.ToJsonString(), out _, out var problem), path);
            Assert.Contains("malformed result document", problem, StringComparison.Ordinal);
        }

        var partial = JsonNode.Parse(text)!;
        partial["result"]!["findingRecords"]!.AsArray().RemoveAt(0);
        Assert.False(SemanticDescriptor.TryParseResult(partial.ToJsonString(), out _, out var alignment));
        Assert.Contains("not aligned", alignment, StringComparison.Ordinal);

        // The descriptor's recorded result is the v1 text it always was: no records in it.
        var descriptor = SemanticDescriptor.Write(Success, value);
        Assert.DoesNotContain("findingRecords", descriptor, StringComparison.Ordinal);
        Assert.Contains("findingRecords", text, StringComparison.Ordinal);
    }

    /// <summary>The serialized facet names are a stable, unique registry covering every enumeration member.</summary>
    [Fact]
    public void FacetNames_AreUniqueAndCoverTheEnumeration()
    {
        var names = SemanticFindingFacets.All.Select(SemanticFindingFacets.Name).ToList();
        Assert.Equal(names.Count, names.Distinct(StringComparer.Ordinal).Count());
        Assert.Equal(Enum.GetValues<SemanticFindingFacet>().Order(), SemanticFindingFacets.All.Order());
        foreach (var facet in Enum.GetValues<SemanticFindingFacet>())
        {
            Assert.True(SemanticFindingFacets.TryParse(SemanticFindingFacets.Name(facet), out var parsed));
            Assert.Equal(facet, parsed);
        }
    }
}
