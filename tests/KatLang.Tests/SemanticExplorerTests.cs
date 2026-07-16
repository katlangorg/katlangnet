using System.Text.Json;

namespace KatLang.Tests;

/// <summary>
/// Small-state semantic explorer: sends every corpus value through every
/// receiver template and enforces the boundary invariants structurally
/// (raw result trees and emitted counts, never display text alone).
///
/// Categories checked here: UnexpectedWrapper/UnwritableValue (orphan
/// singleton nodes), DisplayCollision, DisplayNotReconstructable,
/// CountDisagreement, EqualityInstability, IndexingInstability,
/// BoundaryReentryChange, UnexpectedFlattening, DroppedVisibleEmpty,
/// SpreadDepthMismatch, LexicalDotMismatch, BuiltinBoundaryMismatch,
/// UndocumentedException. LeanCSharpDivergence is enforced by the generated
/// artifact lean/SemanticExplorerCases.lean (see SemanticExplorerLeanArtifactTests).
/// </summary>
public class SemanticExplorerTests
{
    private sealed record Finding(string Category, string CaseId, string Detail);

    private static readonly Lazy<IReadOnlyDictionary<string, ExplorerObservation>> LazyObservations =
        new(ObserveAll);

    private static IReadOnlyDictionary<string, ExplorerObservation> Observations => LazyObservations.Value;

    private static IReadOnlyDictionary<string, ExplorerObservation> ObserveAll()
    {
        var map = new Dictionary<string, ExplorerObservation>();
        foreach (var explorerCase in SemanticExplorerCorpus.AllCases())
        {
            ExplorerObservation observation;
            try
            {
                observation = SemanticExplorerHarness.Observe(explorerCase);
            }
            catch (Exception ex)
            {
                observation = new ExplorerObservation(
                    explorerCase.Id, explorerCase.Source, "exception",
                    null, null, null, ex.GetType().Name + ": " + ex.Message, null);
            }

            map[explorerCase.Id] = observation;
        }

        return map;
    }

    private static ExplorerObservation Obs(string templateId, string valueId)
        => Observations[$"{templateId}__{valueId}"];

    [Fact]
    public void SemanticExplorer_AllInvariantsHold()
    {
        var findings = ComputeFindings();
        WriteMachineReadableReport(findings);

        if (findings.Count == 0)
            return;

        var minimized = MinimizePerCategory(findings);
        var lines = minimized
            .Take(50)
            .Select(f => $"[{f.Category}] {f.CaseId}: {f.Detail}");
        Assert.Fail(
            $"{findings.Count} semantic-explorer invariant finding(s); smallest reproducer per (template, category) first:\n"
            + string.Join("\n", lines));
    }

    // ----- Finding computation ------------------------------------------------

    private static List<Finding> ComputeFindings()
    {
        var findings = new List<Finding>();

        foreach (var observation in Observations.Values)
        {
            if (observation.Outcome == "exception")
            {
                findings.Add(new Finding("UndocumentedException", observation.CaseId, observation.ErrorCategory ?? ""));
                continue;
            }

            if (observation.Outcome != "ok")
                continue;

            var orphans = SemanticExplorerHarness.SingletonNodeCount(observation.Value!);
            if (orphans > 0)
            {
                findings.Add(new Finding(
                    "UnexpectedWrapper", observation.CaseId,
                    $"raw {observation.Raw} contains {orphans} literal-unwritable singleton sequence node(s)"));
            }

            CheckDisplayRoundTrip(observation, findings);
        }

        CheckDisplayCollisions(findings);

        foreach (var (valueId, _) in SemanticExplorerCorpus.Values)
        {
            if (Obs("capture", valueId).Outcome != "ok")
                continue; // parse-level value; typed outcome recorded elsewhere

            CheckValueFamily(valueId, findings);
        }

        CheckInternalNodeCases(findings);

        return findings;
    }

    /// <summary>
    /// InternalNodeSurfaceHazard: every direct internal-node case (currently
    /// Expr.SequenceConstruct) is compared against its surface counterpart.
    /// Cases declared IntentionallyDifferent must stay different — if they
    /// become equal, either the parser started routing surface syntax through
    /// the internal node or the internal semantics changed; both require
    /// review. Cases declared IntentionallyEqual must stay equal.
    /// </summary>
    private static void CheckInternalNodeCases(List<Finding> findings)
    {
        foreach (var internalCase in SemanticExplorerCorpus.InternalNodeCases())
        {
            ExplorerObservation internalObs;
            try
            {
                internalObs = SemanticExplorerHarness.ObserveAst(internalCase.Id, internalCase.RootOutput());
            }
            catch (Exception ex)
            {
                findings.Add(new Finding("InternalNodeSurfaceHazard", $"internal__{internalCase.Id}",
                    $"internal-node evaluation threw {ex.GetType().Name}: {ex.Message}"));
                continue;
            }

            var surfaceObs = SemanticExplorerHarness.Observe(
                $"internal__{internalCase.Id}@surface", internalCase.SurfaceCounterpart);

            var equal = internalObs.Outcome == surfaceObs.Outcome
                && internalObs.Raw == surfaceObs.Raw
                && internalObs.Emitted == surfaceObs.Emitted;

            if (internalCase.Relation == InternalNodeRelation.IntentionallyEqual && !equal)
            {
                findings.Add(new Finding("InternalNodeSurfaceHazard", $"internal__{internalCase.Id}",
                    $"expected internal node to MATCH surface '{internalCase.SurfaceCounterpart}' " +
                    $"but observed {internalObs.Neutral} vs {surfaceObs.Neutral}"));
            }
            else if (internalCase.Relation == InternalNodeRelation.IntentionallyDifferent && equal)
            {
                findings.Add(new Finding("InternalNodeSurfaceHazard", $"internal__{internalCase.Id}",
                    $"internal Expr.SequenceConstruct semantics and surface '{internalCase.SurfaceCounterpart}' " +
                    $"now agree on {internalObs.Neutral}; they are intentionally different " +
                    "(the internal node drops () leaves; written parentheses never do) — " +
                    "surface syntax may have started routing through the internal node"));
            }
        }
    }

    private static void CheckDisplayRoundTrip(ExplorerObservation observation, List<Finding> findings)
    {
        // Strings display without quotes by documented design; string display
        // round-tripping is an explicit non-goal.
        if (ContainsString(observation.Value!))
            return;

        if (observation.Emitted == 0)
        {
            // A zero-item output displays as no rows. The empty display is not
            // a parseable program (documented `()...` edge); require exactly
            // the empty display so the exemption stays as narrow as written.
            if (observation.Display != "")
            {
                findings.Add(new Finding(
                    "DisplayNotReconstructable", observation.CaseId,
                    $"zero-emitted output displayed as {observation.Display!}"));
            }

            return;
        }

        ExplorerObservation reparsed;
        try
        {
            reparsed = SemanticExplorerHarness.Observe(observation.CaseId + "@reparse", observation.Display!);
        }
        catch (Exception ex)
        {
            findings.Add(new Finding(
                "DisplayNotReconstructable", observation.CaseId,
                $"display '{observation.Display}' threw {ex.GetType().Name} on re-parse"));
            return;
        }

        if (reparsed.Outcome != "ok" || reparsed.Raw != observation.Raw || reparsed.Emitted != observation.Emitted)
        {
            findings.Add(new Finding(
                "DisplayNotReconstructable", observation.CaseId,
                $"display '{observation.Display}' re-parses to {reparsed.Neutral}, original {observation.Neutral}"));
        }
    }

    private static void CheckDisplayCollisions(List<Finding> findings)
    {
        var byDisplay = Observations.Values
            .Where(o => o.Outcome == "ok")
            .GroupBy(o => o.Display!);

        foreach (var group in byDisplay)
        {
            var shapes = group.Select(o => (o.Raw, o.Emitted)).Distinct().ToList();
            if (shapes.Count > 1)
            {
                var examples = shapes
                    .Select(s => group.First(o => (o.Raw, o.Emitted) == s))
                    .Select(o => $"{o.CaseId}={o.Neutral}");
                findings.Add(new Finding(
                    "DisplayCollision", group.Select(o => o.CaseId).First(),
                    $"display '{group.Key}' produced by inequivalent values: {string.Join(" vs ", examples)}"));
            }
        }
    }

    private static void CheckValueFamily(string valueId, List<Finding> findings)
    {
        var captured = Obs("capture", valueId);
        var capturedValue = captured.Value!;
        var items = capturedValue.ToItems();
        // Spread opens ONE boundary of either structure kind (sequence OR
        // exact list); the non-spread item view keeps lists opaque.
        var spreadItems = capturedValue.SpreadItems();
        var isListValue = capturedValue is Result.ListValue;
        // Builtin collection binding does not accept list values yet
        // (deferred to the follow-up builtin work): a list anywhere in the
        // bound item supply is a targeted type error.
        var builtinItemsContainList = items.Any(static item => item is Result.ListValue);
        var spreadSupplyContainsList = spreadItems.Any(static item => item is Result.ListValue);

        // Every plain access / one-value boundary must observe the identical
        // captured value with emitted count 1.
        AssertSame(findings, "LexicalDotMismatch", valueId, captured, "dotAccess", "dotAccessCall", "captureCall");
        AssertSame(findings, "BoundaryReentryChange", valueId, captured, "identity", "identityTwice", "propChain", "fixed", "root", "seqWrapSolo");
        AssertSame(findings, "BoundaryReentryChange", valueId, captured, "variadic", "variadicViaProp");

        // The grouped/spread coincidence `F(x) == F(x...)` for a rest-only
        // callee is SEQUENCE-specific: canonical capture erases a redundant
        // sequence boundary but never a list boundary, so spreading a lone
        // list re-captures as the sequence of its elements.
        if (!isListValue)
        {
            AssertSame(findings, "BoundaryReentryChange", valueId, captured, "variadicSpread");
        }
        else
        {
            var variadicSpread = Obs("variadicSpread", valueId);
            var expectedRecapture = Result.FromItems(spreadItems);
            if (variadicSpread.Outcome != "ok"
                || !Result.ValueComparer.Equals(variadicSpread.Value, expectedRecapture))
            {
                findings.Add(new Finding(
                    "BoundaryReentryChange", variadicSpread.CaseId,
                    $"expected list spread to re-capture as {SemanticExplorerHarness.Neutral(expectedRecapture)}, observed {variadicSpread.Neutral}"));
            }
        }

        // count(...) vs .count observe the bound item supply; a list in the
        // supply is the deferred-builtin type error, and `count(x...)` counts
        // the spread-opened supply instead.
        foreach (var template in new[] { "count", "dotCount", "literalDotCount" })
        {
            var observation = Obs(template, valueId);
            if (builtinItemsContainList)
            {
                ExpectBuiltinListDeferred(findings, observation);
            }
            else if (observation.Outcome != "ok" || observation.Raw != items.Count.ToString())
            {
                findings.Add(new Finding(
                    "CountDisagreement", observation.CaseId,
                    $"expected {items.Count}, observed {observation.Neutral}"));
            }
        }

        // `count(x...)` counts the spread-opened supply, to which builtin
        // collection binding applies its own singleton-boundary normalization
        // (a supply of exactly one grouped SEQUENCE value is that collection).
        var countSpread = Obs("countSpread", valueId);
        var spreadSupplyAsCollection = spreadItems is [Result.SequenceValue(var loneSeqItems)]
            ? loneSeqItems
            : spreadItems;
        if (spreadSupplyContainsList)
        {
            ExpectBuiltinListDeferred(findings, countSpread);
        }
        else if (countSpread.Outcome != "ok" || countSpread.Raw != spreadSupplyAsCollection.Count.ToString())
        {
            findings.Add(new Finding(
                "CountDisagreement", countSpread.CaseId,
                $"expected {spreadSupplyAsCollection.Count}, observed {countSpread.Neutral}"));
        }

        // Structural equality is reflexive and construction-path independent.
        ExpectAtom(findings, "EqualityInstability", Obs("eqSelf", valueId), 1);
        ExpectAtom(findings, "EqualityInstability", Obs("neqSelf", valueId), 0);
        ExpectAtom(findings, "EqualityInstability", Obs("eqIdentity", valueId), 1);

        // Spread opens exactly one layer: item count and recombined value.
        // For sequences the re-captured value is the captured value itself;
        // for lists it is the canonical sequence of the elements.
        var spreadRoot = Obs("spreadRoot", valueId);
        var expectedSpreadValue = Result.FromItems(spreadItems);
        var expectedSpreadRaw = SemanticExplorerHarness.Neutral(expectedSpreadValue);
        if (spreadRoot.Outcome != "ok"
            || spreadRoot.Emitted != spreadItems.Count
            || spreadRoot.Raw != expectedSpreadRaw)
        {
            findings.Add(new Finding(
                "SpreadDepthMismatch", spreadRoot.CaseId,
                $"expected raw {expectedSpreadRaw} n={spreadItems.Count}, observed {spreadRoot.Neutral}"));
        }

        // A non-spread value stays one visible item; nested structure intact.
        var wrapPair = Obs("seqWrapPair", valueId);
        var expectedWrap = new Result.SequenceValue([capturedValue, new Result.Atom(99)]);
        if (wrapPair.Outcome != "ok" || !Result.ValueComparer.Equals(wrapPair.Value, expectedWrap))
        {
            var category = capturedValue is Result.SequenceValue { Items.Count: 0 }
                ? "DroppedVisibleEmpty"
                : "UnexpectedFlattening";
            findings.Add(new Finding(
                category, wrapPair.CaseId,
                $"expected {SemanticExplorerHarness.Neutral(expectedWrap)}, observed {wrapPair.Neutral}"));
        }

        // Spread into a sequence literal splices exactly the one-layer items.
        var spreadInSeq = Obs("spreadInSeq", valueId);
        var expectedSplice = SemanticExplorerHarness.ShallowCombine([.. spreadItems, new Result.Atom(99)]);
        if (spreadInSeq.Outcome != "ok" || !Result.ValueComparer.Equals(spreadInSeq.Value, expectedSplice))
        {
            findings.Add(new Finding(
                "SpreadDepthMismatch", spreadInSeq.CaseId,
                $"expected {SemanticExplorerHarness.Neutral(expectedSplice)}, observed {spreadInSeq.Neutral}"));
        }

        // Indexing: one-level projection with the documented root row bump
        // (a non-spread output slot always contributes at least one row).
        foreach (var (template, index) in new[] { ("index0", 0), ("index1", 1), ("indexBig", 9) })
        {
            var observation = Obs(template, valueId);
            var projected = capturedValue.SelectProjected(index);
            if (projected is null)
            {
                if (observation.Outcome != "err" || observation.ErrorCategory != "index")
                {
                    findings.Add(new Finding(
                        "IndexingInstability", observation.CaseId,
                        $"expected err index, observed {observation.Neutral}"));
                }
            }
            else if (observation.Outcome != "ok"
                || !Result.ValueComparer.Equals(observation.Value, projected.Value.Value)
                || observation.Emitted != Math.Max(1, projected.Value.EmittedCount))
            {
                findings.Add(new Finding(
                    "IndexingInstability", observation.CaseId,
                    $"expected raw {SemanticExplorerHarness.Neutral(projected.Value.Value)} " +
                    $"n={Math.Max(1, projected.Value.EmittedCount)}, observed {observation.Neutral}"));
            }
        }

        CheckCollectionBuiltins(valueId, captured, items, findings);
    }

    private static void CheckCollectionBuiltins(
        string valueId,
        ExplorerObservation captured,
        IReadOnlyList<Result> items,
        List<Finding> findings)
    {
        // Builtin collection binding does not accept list values yet: a list
        // anywhere in the bound item supply is the deferred-builtin type
        // error, uniformly across the collection builtins.
        if (items.Any(static item => item is Result.ListValue))
        {
            foreach (var template in new[]
                     {
                         "take1", "take9", "skip1", "filterKeep", "distinct", "order",
                         "mapId", "takeCapture", "takeIdentity", "takeVariadic", "takeCount",
                     })
            {
                ExpectBuiltinListDeferred(findings, Obs(template, valueId));
            }

            // `atoms` flattens through Result.ToAtoms directly (it never binds
            // an item supply), so lists are omitted like strings rather than
            // rejected — checked below with the shared expectation.
            var atomsWithList = Obs("atoms", valueId);
            var expectedAtomsWithList = Result.FromItems(
                captured.Value!.ToAtoms().Select(a => (Result)new Result.Atom(a)));
            if (atomsWithList.Outcome != "ok"
                || !Result.ValueComparer.Equals(atomsWithList.Value, expectedAtomsWithList))
            {
                findings.Add(new Finding(
                    "BuiltinBoundaryMismatch", atomsWithList.CaseId,
                    $"expected {SemanticExplorerHarness.Neutral(expectedAtomsWithList)}, observed {atomsWithList.Neutral}"));
            }

            return;
        }

        // take/skip/distinct/filter keep original items and recombine with the
        // shallow single-survivor boundary erasure; expected values are
        // computed structurally from the captured value's one-layer items.
        ExpectCombined(findings, Obs("take1", valueId), items.Take(1).ToList());
        ExpectCombined(findings, Obs("take9", valueId), items);
        ExpectCombined(findings, Obs("skip1", valueId), items.Skip(1).ToList());
        ExpectCombined(findings, Obs("filterKeep", valueId), items);
        ExpectCombined(findings, Obs("distinct", valueId), items.Distinct(Result.ValueComparer).ToList());

        var allAtoms = items.All(i => i is Result.Atom);
        var order = Obs("order", valueId);
        if (allAtoms)
        {
            var sorted = items.Cast<Result.Atom>().OrderBy(a => a.Value).Cast<Result>().ToList();
            ExpectCombined(findings, order, sorted);
        }
        else if (order.Outcome != "err")
        {
            findings.Add(new Finding(
                "BuiltinBoundaryMismatch", order.CaseId,
                $"expected error on non-numeric items, observed {order.Neutral}"));
        }

        var mapId = Obs("mapId", valueId);
        if (allAtoms)
        {
            ExpectCombined(findings, mapId, items);
        }
        else if (mapId.Outcome != "err")
        {
            findings.Add(new Finding(
                "BuiltinBoundaryMismatch", mapId.CaseId,
                $"expected single-element contract error, observed {mapId.Neutral}"));
        }

        var atoms = Obs("atoms", valueId);
        var expectedAtoms = Result.FromItems(
            captured.Value!.ToAtoms().Select(a => (Result)new Result.Atom(a)));
        if (atoms.Outcome != "ok" || !Result.ValueComparer.Equals(atoms.Value, expectedAtoms))
        {
            findings.Add(new Finding(
                "BuiltinBoundaryMismatch", atoms.CaseId,
                $"expected {SemanticExplorerHarness.Neutral(expectedAtoms)}, observed {atoms.Neutral}"));
        }

        // A builtin result re-enters every boundary unchanged.
        AssertSame(findings, "BuiltinBoundaryMismatch", valueId, Obs("take1", valueId),
            "takeCapture", "takeIdentity", "takeVariadic");

        // The single-survivor boundary erasure means count() of a one-item
        // take observes the survivor's own contents: count(take(((1,2),3),1))
        // is 2, and a lone kept `()` counts 0 (documented #133 semantics).
        var takeCount = Obs("takeCount", valueId);
        var expectedTakeCount = SemanticExplorerHarness
            .ShallowCombine(items.Take(1).ToList())
            .ToItems().Count;
        if (takeCount.Outcome != "ok" || takeCount.Raw != expectedTakeCount.ToString())
        {
            findings.Add(new Finding(
                "CountDisagreement", takeCount.CaseId,
                $"expected {expectedTakeCount}, observed {takeCount.Neutral}"));
        }
    }

    /// <summary>
    /// A collection builtin observing a list value in its bound item supply
    /// reports the deferred-list type error (final builtin list semantics are
    /// a follow-up; only explicit spread supplies list elements today).
    /// </summary>
    private static void ExpectBuiltinListDeferred(List<Finding> findings, ExplorerObservation observation)
    {
        if (observation.Outcome != "err" || observation.ErrorCategory != "type")
        {
            findings.Add(new Finding(
                "BuiltinBoundaryMismatch", observation.CaseId,
                $"expected the deferred-list builtin type error, observed {observation.Neutral}"));
        }
    }

    private static void ExpectCombined(List<Finding> findings, ExplorerObservation observation, IReadOnlyList<Result> keptItems)
    {
        var expected = SemanticExplorerHarness.ShallowCombine(keptItems);
        var expectedEmitted = expected is Result.SequenceValue { Items.Count: 0 } ? 0 : 1;
        _ = expectedEmitted; // collection results re-count at the boundary; root slot shows 1 row minimum
        if (observation.Outcome != "ok" || !Result.ValueComparer.Equals(observation.Value, expected))
        {
            findings.Add(new Finding(
                "BuiltinBoundaryMismatch", observation.CaseId,
                $"expected {SemanticExplorerHarness.Neutral(expected)}, observed {observation.Neutral}"));
        }
    }

    private static void ExpectAtom(List<Finding> findings, string category, ExplorerObservation observation, int expected)
    {
        if (observation.Outcome != "ok" || observation.Raw != expected.ToString())
        {
            findings.Add(new Finding(
                category, observation.CaseId, $"expected {expected}, observed {observation.Neutral}"));
        }
    }

    private static void AssertSame(
        List<Finding> findings,
        string category,
        string valueId,
        ExplorerObservation reference,
        params string[] templates)
    {
        foreach (var template in templates)
        {
            var observation = Obs(template, valueId);
            if (observation.Outcome != reference.Outcome
                || observation.Raw != reference.Raw
                || observation.Emitted != reference.Emitted)
            {
                findings.Add(new Finding(
                    category, observation.CaseId,
                    $"observed {observation.Neutral}, but {reference.CaseId} observed {reference.Neutral}"));
            }
        }
    }

    private static bool ContainsString(Result result) => result switch
    {
        Result.Str => true,
        Result.SequenceValue g => g.Items.Any(ContainsString),
        Result.ListValue l => l.Items.Any(ContainsString),
        _ => false,
    };

    // ----- Minimization & report -----------------------------------------------

    /// <summary>
    /// Present the shortest-source failing cell per (template, category) first;
    /// the full finding list is preserved in the machine-readable report.
    /// </summary>
    private static List<Finding> MinimizePerCategory(List<Finding> findings)
        => findings
            .GroupBy(f => (f.Category, Template: f.CaseId.Split("__")[0]))
            .Select(g => g.OrderBy(f => Observations.TryGetValue(f.CaseId, out var o) ? o.Source.Length : int.MaxValue).First())
            .ToList();

    private static void WriteMachineReadableReport(List<Finding> findings)
    {
        var allCases = SemanticExplorerCorpus.AllCases();
        var report = new
        {
            corpus = "SemanticExplorerCorpus",
            caseCount = Observations.Count,
            // Authoritative partition, computed from the live collections so
            // documented totals cannot drift (see the accounting table in
            // docs/design/sequence-boundary-audit-2026-07.md).
            partition = new
            {
                surfaceCases = Observations.Count,
                templateCases = Observations.Values.Count(o => !o.CaseId.StartsWith("special__", StringComparison.Ordinal)),
                specialCases = Observations.Values.Count(o => o.CaseId.StartsWith("special__", StringComparison.Ordinal)),
                byOutcome = Observations.Values
                    .GroupBy(o => o.Outcome)
                    .OrderBy(g => g.Key, StringComparer.Ordinal)
                    .ToDictionary(g => g.Key, g => g.Count()),
                leanRepresentable = allCases.Count(c => c.LeanProgram is not null),
                leanExcludedParseLevel = allCases.Count(c => c.LeanProgram is null),
                internalNodeCases = SemanticExplorerCorpus.InternalNodeCases().Count,
            },
            findingCount = findings.Count,
            findings = findings.Select(f => new
            {
                f.Category,
                f.CaseId,
                f.Detail,
                Source = Observations.TryGetValue(f.CaseId, out var o) ? o.Source : null,
            }),
            cases = Observations.Values.OrderBy(o => o.CaseId, StringComparer.Ordinal).Select(o => new
            {
                id = o.CaseId,
                source = o.Source,
                outcome = o.Outcome,
                neutral = o.Neutral,
                display = o.Display,
            }),
            internalNodeCases = SemanticExplorerCorpus.InternalNodeCases().Select(c =>
            {
                string internalNeutral;
                try
                {
                    internalNeutral = SemanticExplorerHarness.ObserveAst(c.Id, c.RootOutput()).Neutral;
                }
                catch (Exception ex)
                {
                    internalNeutral = "exception " + ex.GetType().Name;
                }

                return new
                {
                    id = "internal__" + c.Id,
                    description = c.Description,
                    node = "Expr.SequenceConstruct",
                    internalNeutral,
                    surfaceCounterpart = c.SurfaceCounterpart,
                    surfaceNeutral = SemanticExplorerHarness
                        .Observe("internal__" + c.Id + "@surface", c.SurfaceCounterpart).Neutral,
                    relation = c.Relation.ToString(),
                };
            }),
        };

        var path = Path.Combine(AppContext.BaseDirectory, "SemanticExplorerReport.json");
        File.WriteAllText(path, JsonSerializer.Serialize(report, new JsonSerializerOptions { WriteIndented = true }));
    }

    // ----- Anchor regressions ---------------------------------------------------
    // Focused counted pins for the boundary cells the explorer's Phase-1 review
    // identified as load-bearing; failures here localize faster than the full
    // invariant sweep.

    public static TheoryData<string, string> AnchorCases => new()
    {
        // written form            neutral observation
        { "()", "ok raw=S[] n=1" },
        { "(())", "ok raw=S[] n=1" },
        { "(1)", "ok raw=1 n=1" },
        { "((1))", "ok raw=1 n=1" },
        { "(((1, 2)))", "ok raw=S[1, 2] n=1" },
        { "((), ())", "ok raw=S[S[], S[]] n=1" },
        { "((), 1)", "ok raw=S[S[], 1] n=1" },
        { "((1, 2), ())", "ok raw=S[S[1, 2], S[]] n=1" },
        { "1, 2", "ok raw=S[1, 2] n=2" },
        { "(1, 2)...", "ok raw=S[1, 2] n=2" },
        { "()...", "ok raw=S[] n=0" },
        { "(()..., 99)", "ok raw=99 n=1" },
        { "((), 99)", "ok raw=S[S[], 99] n=1" },
        { "take(((1, 2), (3, 4)), 1)", "ok raw=S[1, 2] n=1" },
        { "distinct((), ())", "ok raw=S[] n=1" },
        { "take((), (), 2)", "ok raw=S[S[], S[]] n=1" },
        { "x = ((1, 2), (3, 4))\nx:0", "ok raw=S[1, 2] n=2" },
        { "x = ((), ())\nx:0", "ok raw=S[] n=1" },
        { "P = (), 99\nP", "ok raw=S[S[], 99] n=1" },
        { "F(a...) = a\nF(1, 2, 3)", "ok raw=S[1, 2, 3] n=1" },
        { "() > 1", "ok raw=1 n=1" },
        { "() == (())", "ok raw=1 n=1" },
        { "x = (1, 2)\n(x..., 99)", "ok raw=S[1, 2, 99] n=1" },
        { "(1..., (), 2...)", "ok raw=S[1, S[], 2] n=1" },
        { "A = (1, 2)\nA..., 99", "ok raw=S[1, 2, 99] n=3" },
    };

    [Theory]
    [MemberData(nameof(AnchorCases))]
    public void AnchorCase_ObservesPinnedRawStructureAndCount(string source, string expectedNeutral)
    {
        var observation = SemanticExplorerHarness.Observe("anchor", source);
        Assert.Equal(expectedNeutral, observation.Neutral);
    }
}
