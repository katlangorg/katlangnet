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
        // exact list); the non-spread item view keeps lists opaque. The
        // builtin collection view coincides with the spread view for a lone
        // bound value: exactly one outer sequence or list boundary opens.
        var spreadItems = capturedValue.SpreadItems();
        var builtinSupply = spreadItems;
        var isListValue = capturedValue is Result.ListValue;

        // Every plain access / one-value boundary must observe the identical
        // captured value with emitted count 1.
        AssertSame(findings, "LexicalDotMismatch", valueId, captured, "dotAccess", "dotAccessCall", "captureCall");
        AssertSame(findings, "BoundaryReentryChange", valueId, captured, "identity", "identityTwice", "propChain", "fixed", "root", "seqWrapSolo");

        // Rest binding COLLECTS: a rest-only callee binds its ONE grouped
        // argument as the one-element exact list holding the value
        // (`F(...x) = x` with `F(V)` observes `[V]`), never the value itself —
        // the old grouped/singleton coincidence is gone for every value kind.
        var expectedCollectedOne = new Result.ListValue([capturedValue]);
        foreach (var template in new[] { "variadic", "variadicViaProp" })
        {
            var observation = Obs(template, valueId);
            if (observation.Outcome != "ok"
                || !Result.ValueComparer.Equals(observation.Value, expectedCollectedOne)
                || observation.Emitted != 1)
            {
                findings.Add(new Finding(
                    "BoundaryReentryChange", observation.CaseId,
                    $"expected rest to collect {SemanticExplorerHarness.Neutral(expectedCollectedOne)} n=1, observed {observation.Neutral}"));
            }
        }

        // The spread call `F(V...)` collects the spread-opened items as an
        // exact list, uniformly for sequences and lists (open/collect round
        // trip: spreading a list re-collects the same list).
        var variadicSpread = Obs("variadicSpread", valueId);
        var expectedCollectedSpread = new Result.ListValue(spreadItems);
        if (variadicSpread.Outcome != "ok"
            || !Result.ValueComparer.Equals(variadicSpread.Value, expectedCollectedSpread)
            || variadicSpread.Emitted != 1)
        {
            findings.Add(new Finding(
                "BoundaryReentryChange", variadicSpread.CaseId,
                $"expected spread supply to collect as {SemanticExplorerHarness.Neutral(expectedCollectedSpread)} n=1, observed {variadicSpread.Neutral}"));
        }

        // count(...) vs .count observe the bound collection through the shared
        // builtin collection view: a lone sequence OR list value opens one
        // outer boundary; any other value is one item.
        foreach (var template in new[] { "count", "dotCount", "literalDotCount" })
        {
            var observation = Obs(template, valueId);
            if (observation.Outcome != "ok" || observation.Raw != builtinSupply.Count.ToString())
            {
                findings.Add(new Finding(
                    "CountDisagreement", observation.CaseId,
                    $"expected {builtinSupply.Count}, observed {observation.Neutral}"));
            }
        }

        // `count(x...)` supplies the spread-opened items as ORDINARY argument
        // slots that obey count's fixed one-parameter arity: exactly one
        // opened item binds the collection parameter (and is then interpreted
        // through the post-binding one-level collection view), while zero or
        // several opened items are an ordinary arity error.
        var countSpread = Obs("countSpread", valueId);
        if (spreadItems.Count == 1)
        {
            var expectedSpreadCount = spreadItems[0].SpreadItems().Count;
            if (countSpread.Outcome != "ok" || countSpread.Raw != expectedSpreadCount.ToString())
            {
                findings.Add(new Finding(
                    "CountDisagreement", countSpread.CaseId,
                    $"expected {expectedSpreadCount}, observed {countSpread.Neutral}"));
            }
        }
        else if (countSpread.Outcome != "err" || countSpread.ErrorCategory != "arity")
        {
            findings.Add(new Finding(
                "CountDisagreement", countSpread.CaseId,
                $"expected an ordinary arity error for {spreadItems.Count} spread-opened arguments, observed {countSpread.Neutral}"));
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

        CheckCollectionBuiltins(valueId, captured, builtinSupply, findings);
    }

    private static void CheckCollectionBuiltins(
        string valueId,
        ExplorerObservation captured,
        IReadOnlyList<Result> builtinSupply,
        List<Finding> findings)
    {
        // Collection-producing builtins materialize ONE exact immutable list
        // of the kept/projected supply items: zero items form [], a single
        // kept item is never erased, and nested sequence/list values stay
        // exact elements. The supply itself is the builtin collection view of
        // the captured value (one outer sequence or list boundary opened).
        ExpectExactList(findings, Obs("take1", valueId), builtinSupply.Take(1).ToList());
        ExpectExactList(findings, Obs("take9", valueId), builtinSupply);
        ExpectExactList(findings, Obs("skip1", valueId), builtinSupply.Skip(1).ToList());
        ExpectExactList(findings, Obs("filterKeep", valueId), builtinSupply);
        ExpectExactList(findings, Obs("distinct", valueId), builtinSupply.Distinct(Result.ValueComparer).ToList());

        var allAtoms = builtinSupply.All(i => i is Result.Atom);
        var order = Obs("order", valueId);
        if (allAtoms)
        {
            var sorted = builtinSupply.Cast<Result.Atom>().OrderBy(a => a.Value).Cast<Result>().ToList();
            ExpectExactList(findings, order, sorted);
        }
        else if (order.Outcome != "err")
        {
            findings.Add(new Finding(
                "BuiltinBoundaryMismatch", order.CaseId,
                $"expected error on non-numeric items, observed {order.Neutral}"));
        }

        // The identity map callback `M(a) = a` binds each supply item through
        // ordinary counted callback projection: an atom or exact list item is
        // one bound value and maps to itself, while a sequence-valued item
        // projects to a different count and fails the strict single-element
        // transform contract (empty `()` items project zero values).
        var mapId = Obs("mapId", valueId);
        var mapIdBindsOneValuePerItem = builtinSupply.All(static i => i is Result.Atom or Result.ListValue);
        if (mapIdBindsOneValuePerItem)
        {
            ExpectExactList(findings, mapId, builtinSupply);
        }
        else if (mapId.Outcome != "err")
        {
            findings.Add(new Finding(
                "BuiltinBoundaryMismatch", mapId.CaseId,
                $"expected single-element contract error, observed {mapId.Neutral}"));
        }

        // `atoms` recursively collects numeric atoms through BOTH sequence
        // and exact list boundaries (depth-first, left-to-right) and
        // materializes them as ONE exact immutable list. Truth testing stays
        // list-opaque and is pinned separately. The expectation uses an
        // independent local traversal so the sweep checks the runtime
        // collector rather than restating it.
        var atoms = Obs("atoms", valueId);
        var expectedAtoms = new Result.ListValue(CollectNumericAtomsRecursively(captured.Value!));
        if (atoms.Outcome != "ok" || !Result.ValueComparer.Equals(atoms.Value, expectedAtoms))
        {
            findings.Add(new Finding(
                "BuiltinBoundaryMismatch", atoms.CaseId,
                $"expected {SemanticExplorerHarness.Neutral(expectedAtoms)}, observed {atoms.Neutral}"));
        }

        // A builtin result re-enters value boundaries unchanged (a list value
        // is one value for capture and identity calls), while a rest binding
        // collects it as the one-element list holding it.
        var take1 = Obs("take1", valueId);
        AssertSame(findings, "BuiltinBoundaryMismatch", valueId, take1,
            "takeCapture", "takeIdentity");
        var takeVariadic = Obs("takeVariadic", valueId);
        if (take1.Outcome == "ok")
        {
            var expectedTakeCollected = new Result.ListValue([take1.Value!]);
            if (takeVariadic.Outcome != "ok"
                || !Result.ValueComparer.Equals(takeVariadic.Value, expectedTakeCollected)
                || takeVariadic.Emitted != 1)
            {
                findings.Add(new Finding(
                    "BuiltinBoundaryMismatch", takeVariadic.CaseId,
                    $"expected rest to collect {SemanticExplorerHarness.Neutral(expectedTakeCollected)} n=1, observed {takeVariadic.Neutral}"));
            }
        }
        else if (takeVariadic.Outcome != take1.Outcome)
        {
            findings.Add(new Finding(
                "BuiltinBoundaryMismatch", takeVariadic.CaseId,
                $"observed {takeVariadic.Neutral}, but {take1.CaseId} observed {take1.Neutral}"));
        }

        // count() of a take(x, 1) result opens exactly the one list boundary
        // that take materialized, so it counts the kept items: 1 when the
        // supply had any item, 0 for an empty supply — never the survivor's
        // own contents (exact lists have no single-survivor erasure).
        var takeCount = Obs("takeCount", valueId);
        var expectedTakeCount = builtinSupply.Count == 0 ? 0 : 1;
        if (takeCount.Outcome != "ok" || takeCount.Raw != expectedTakeCount.ToString())
        {
            findings.Add(new Finding(
                "CountDisagreement", takeCount.CaseId,
                $"expected {expectedTakeCount}, observed {takeCount.Neutral}"));
        }
    }

    /// <summary>
    /// Independent model of the `atoms` builtin's collection rule: numeric
    /// atoms gathered depth-first, left-to-right, through both sequence and
    /// exact list boundaries; strings and other leaves contribute none.
    /// </summary>
    private static List<Result> CollectNumericAtomsRecursively(Result value) => value switch
    {
        Result.Atom(var n) => [new Result.Atom(n)],
        Result.SequenceValue(var items) => items.SelectMany(CollectNumericAtomsRecursively).ToList(),
        Result.ListValue(var items) => items.SelectMany(CollectNumericAtomsRecursively).ToList(),
        _ => [],
    };

    private static void ExpectExactList(List<Finding> findings, ExplorerObservation observation, IReadOnlyList<Result> keptItems)
    {
        var expected = SemanticExplorerHarness.ExpectedCollectionList(keptItems);
        if (observation.Outcome != "ok"
            || !Result.ValueComparer.Equals(observation.Value, expected)
            || observation.Emitted != 1)
        {
            findings.Add(new Finding(
                "BuiltinBoundaryMismatch", observation.CaseId,
                $"expected {SemanticExplorerHarness.Neutral(expected)} n=1, observed {observation.Neutral}"));
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
        { "take(((1, 2), (3, 4)), 1)", "ok raw=L[S[1, 2]] n=1" },
        { "distinct(((), ()))", "ok raw=L[S[]] n=1" },
        { "take(((), ()), 2)", "ok raw=L[S[], S[]] n=1" },
        { "distinct((), ())", "err arity" },
        { "take((), (), 2)", "err arity" },
        { "count([1, 2, 3])", "ok raw=3 n=1" },
        { "count(1, 2, 3)", "err arity" },
        { "count()", "err arity" },
        { "count([1, 2, 3]...)", "err arity" },
        { "take([1, 2, 3])", "err arity" },
        { "take([1, 2, 3], 0)", "ok raw=L[] n=1" },
        { "take([[1, 2], [3, 4]], 1)", "ok raw=L[L[1, 2]] n=1" },
        { "x = ((1, 2), (3, 4))\nx:0", "ok raw=S[1, 2] n=2" },
        { "x = ((), ())\nx:0", "ok raw=S[] n=1" },
        { "P = (), 99\nP", "ok raw=S[S[], 99] n=1" },
        { "F(...a) = a\nF(1, 2, 3)", "ok raw=L[1, 2, 3] n=1" },
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
