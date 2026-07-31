using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;
using KatLang;

namespace KatLang.Tests.ArityDifferential;

/// <summary>
/// Runner for the generated arity-differential campaign: every case executes
/// through the production front end and evaluator
/// (<see cref="SemanticExplorerHarness.Observe(string, string)"/>, which
/// cross-checks Evaluator.RunCounted against KatLangEngine.Run) and is
/// compared against the expectation computed independently by
/// <see cref="AlgebraOracle"/>. See docs/design/arity-differential-campaign.md.
/// </summary>
public class ArityDifferentialTests
{
    private static readonly IReadOnlyList<DifferentialCase> Matrix = ArityDifferentialMatrix.MatrixCases();
    private static readonly IReadOnlyDictionary<string, DifferentialCase> MatrixById =
        Matrix.ToDictionary(c => c.Id, StringComparer.Ordinal);

    private static readonly IReadOnlyList<RelationalCase> Relational = ArityDifferentialMatrix.RelationalCases();
    private static readonly IReadOnlyDictionary<string, RelationalCase> RelationalById =
        Relational.ToDictionary(c => c.Id, StringComparer.Ordinal);

    private static readonly IReadOnlyList<DiagnosticCase> Diagnostics = ArityDifferentialMatrix.DiagnosticCases();
    private static readonly IReadOnlyDictionary<string, DiagnosticCase> DiagnosticsById =
        Diagnostics.ToDictionary(c => c.Id, StringComparer.Ordinal);

    // Each generated program is observed at most once per test session.
    private static readonly Lazy<IReadOnlyDictionary<string, ExplorerObservation>> Observations =
        new(ObserveAll, LazyThreadSafetyMode.ExecutionAndPublication);

    private static IReadOnlyDictionary<string, ExplorerObservation> ObserveAll()
    {
        var observations = new Dictionary<string, ExplorerObservation>(StringComparer.Ordinal);
        foreach (var differentialCase in Matrix)
            observations[differentialCase.Id] = SemanticExplorerHarness.Observe(differentialCase.Id, differentialCase.Source);
        foreach (var relationalCase in Relational)
        {
            observations[$"{relationalCase.Id}~left"] =
                SemanticExplorerHarness.Observe($"{relationalCase.Id}~left", relationalCase.LeftSource);
            observations[$"{relationalCase.Id}~right"] =
                SemanticExplorerHarness.Observe($"{relationalCase.Id}~right", relationalCase.RightSource);
        }

        return observations;
    }

    // ----- Matrix ---------------------------------------------------------------

    public static TheoryData<string> MatrixIds()
    {
        var data = new TheoryData<string>();
        foreach (var differentialCase in Matrix)
            data.Add(differentialCase.Id);
        return data;
    }

    [Theory]
    [MemberData(nameof(MatrixIds))]
    public void Matrix_RuntimeAgreesWithAlgebraOracle(string caseId)
    {
        var differentialCase = MatrixById[caseId];
        var observation = Observations.Value[caseId];
        if (observation.Neutral != differentialCase.Expected.Neutral)
            Assert.Fail(MatrixFailureReport(differentialCase, observation));
    }

    private static string MatrixFailureReport(DifferentialCase differentialCase, ExplorerObservation observation)
    {
        var report = new StringBuilder();
        report.AppendLine($"ARITY-DIFFERENTIAL MISMATCH: {differentialCase.Id}");
        report.AppendLine($"  receiver={differentialCase.Receiver} form={differentialCase.Form} " +
            $"shape={differentialCase.ShapeId} multiplicity={differentialCase.Multiplicity}");
        report.AppendLine($"  primary law: {differentialCase.PrimaryLaw}");
        report.AppendLine($"    lean: {ReceiverLaws.LeanReference[differentialCase.PrimaryLaw]}");
        report.AppendLine("  source:");
        foreach (var line in differentialCase.Source.Split('\n'))
            report.AppendLine($"    | {line}");
        report.AppendLine("  algebra (oracle steps):");
        foreach (var step in differentialCase.AlgebraTrace)
            report.AppendLine($"    - {step}");
        report.AppendLine($"  expected: {differentialCase.Expected.Neutral}");
        report.AppendLine($"  actual:   {observation.Neutral}" +
            (observation.Display is { } display ? $" (display: {display.ReplaceLineEndings("\\n")})" : ""));
        report.AppendLine($"  difference: {DescribeDifference(differentialCase.Expected.Neutral, observation.Neutral)}");
        if (differentialCase.Notes is { } notes)
            report.AppendLine($"  notes: {notes}");
        return report.ToString();
    }

    private static string DescribeDifference(string expected, string actual)
    {
        var expectedOk = expected.StartsWith("ok ", StringComparison.Ordinal);
        var actualOk = actual.StartsWith("ok ", StringComparison.Ordinal);
        if (expectedOk != actualOk)
            return expectedOk
                ? "the oracle expects a value but the runtime rejected the program (or vice versa) — outcome class differs"
                : "the oracle expects a rejection but the runtime produced a value — outcome class differs";
        if (!expectedOk)
            return "both reject, but with different error categories";

        static (string Raw, string N) Split(string neutral)
        {
            var nIndex = neutral.LastIndexOf(" n=", StringComparison.Ordinal);
            return (neutral[("ok raw=".Length)..nIndex], neutral[(nIndex + 3)..]);
        }

        var (expectedRaw, expectedN) = Split(expected);
        var (actualRaw, actualN) = Split(actual);
        if (expectedRaw != actualRaw && expectedN != actualN)
            return "both the value structure and the emitted count differ";
        if (expectedRaw != actualRaw)
            return "the value structure differs (kind, items, order, or canonicalization) at equal emitted count";
        return "the structural value agrees but the emitted count differs (a value-boundary / supply-count divergence)";
    }

    // ----- Relational families ----------------------------------------------------

    public static TheoryData<string> RelationalIds()
    {
        var data = new TheoryData<string>();
        foreach (var relationalCase in Relational)
            data.Add(relationalCase.Id);
        return data;
    }

    [Theory]
    [MemberData(nameof(RelationalIds))]
    public void Relational_ProgramsRelateAsTheAlgebraPredicts(string caseId)
    {
        var relationalCase = RelationalById[caseId];
        var left = Observations.Value[$"{caseId}~left"];
        var right = Observations.Value[$"{caseId}~right"];

        var failures = new List<string>();
        if (left.Neutral != relationalCase.ExpectedLeft.Neutral)
            failures.Add($"left side diverges from the oracle: expected {relationalCase.ExpectedLeft.Neutral}, actual {left.Neutral}");
        if (right.Neutral != relationalCase.ExpectedRight.Neutral)
            failures.Add($"right side diverges from the oracle: expected {relationalCase.ExpectedRight.Neutral}, actual {right.Neutral}");
        var agree = left.Neutral == right.Neutral;
        if (agree != relationalCase.ExpectAgreement)
            failures.Add(relationalCase.ExpectAgreement
                ? $"the two programs must agree but observed {left.Neutral} vs {right.Neutral}"
                : $"the two programs must stay observably different but both observed {left.Neutral}");

        if (failures.Count == 0)
            return;

        var report = new StringBuilder();
        report.AppendLine($"ARITY-DIFFERENTIAL RELATION VIOLATION: {relationalCase.Id} (family {relationalCase.Family})");
        report.AppendLine($"  shape={relationalCase.ShapeId} multiplicity={relationalCase.Multiplicity} expectAgreement={relationalCase.ExpectAgreement}");
        report.AppendLine($"  primary law: {relationalCase.PrimaryLaw}");
        report.AppendLine($"    lean: {ReceiverLaws.LeanReference[relationalCase.PrimaryLaw]}");
        report.AppendLine("  left source:");
        foreach (var line in relationalCase.LeftSource.Split('\n'))
            report.AppendLine($"    | {line}");
        report.AppendLine("  right source:");
        foreach (var line in relationalCase.RightSource.Split('\n'))
            report.AppendLine($"    | {line}");
        report.AppendLine("  algebra (oracle steps):");
        foreach (var step in relationalCase.AlgebraTrace)
            report.AppendLine($"    - {step}");
        foreach (var failure in failures)
            report.AppendLine($"  FAIL: {failure}");
        Assert.Fail(report.ToString());
    }

    // ----- Diagnostic matrix ---------------------------------------------------------

    public static TheoryData<string> DiagnosticIds()
    {
        var data = new TheoryData<string>();
        foreach (var diagnosticCase in Diagnostics)
            data.Add(diagnosticCase.Id);
        return data;
    }

    [Theory]
    [MemberData(nameof(DiagnosticIds))]
    public void Diagnostic_InvalidFormsAreRejectedWithStableIdentity(string caseId)
    {
        var diagnosticCase = DiagnosticsById[caseId];

        if (diagnosticCase.ExpectedParseDiagnosticFragment is { } fragment)
        {
            var parsed = Parser.Parse(diagnosticCase.Source);
            Assert.True(parsed.HasErrors,
                $"{caseId}: expected a parse-level rejection ({diagnosticCase.PrimaryLaw}), but the source parsed cleanly:\n{diagnosticCase.Source}");
            Assert.True(
                parsed.Diagnostics.Any(d => d.Message.Contains(fragment, StringComparison.OrdinalIgnoreCase)),
                $"{caseId}: no parse diagnostic contains \"{fragment}\"; got: "
                + string.Join(" | ", parsed.Diagnostics.Select(d => d.Message)));
            return;
        }

        var observation = SemanticExplorerHarness.Observe(caseId, diagnosticCase.Source);
        Assert.True(observation.Outcome == "err",
            $"{caseId}: expected evaluation rejection ({diagnosticCase.ExpectedErrorCategory}), observed {observation.Neutral} for:\n{diagnosticCase.Source}");
        Assert.Equal(diagnosticCase.ExpectedErrorCategory, observation.ErrorCategory);
    }

    // ----- Receiver-evaluated-once budget relation -------------------------------------

    [Theory]
    [InlineData("count(range(1, 8))", "range(1, 8).count")]
    [InlineData("Gather(*items) = items\nGather(range(1, 8)*)", "Gather(*items) = items\nrange(1, 8)*.Gather")]
    [InlineData("Gather(*items) = items\nGather(range(1, 8)**)", "Gather(*items) = items\nrange(1, 8)**.Gather")]
    public void ReceiverOnce_DottedSpellingChargesTheSameItemBudgetAsTheDirectRewrite(string direct, string dotted)
    {
        Assert.Equal(SemanticExplorerHarness.Observe("once-direct", direct).Neutral,
            SemanticExplorerHarness.Observe("once-dotted", dotted).Neutral);
        Assert.Equal(RequiredItemSlots(direct), RequiredItemSlots(dotted));
    }

    /// <summary>
    /// Minimal materialization budget under which the program completes — the
    /// double-evaluation probe from DottedReceiverEvaluationTests: a receiver
    /// evaluated twice would charge twice the item slots.
    /// </summary>
    private static long RequiredItemSlots(string source)
    {
        var parsed = Parser.Parse(source);
        Assert.False(parsed.HasErrors,
            $"probe program must parse: {string.Join(" | ", parsed.Diagnostics.Select(d => d.Message))}");
        for (long budget = 1; budget <= 512; budget++)
        {
            var result = Evaluator.Run(new Expr.Block(parsed.Root), new EvaluationLimits { MaxMaterializedItems = budget });
            if (!result.IsError)
                return budget;
        }

        Assert.Fail($"probe program `{source}` never completed within the budget range");
        return -1;
    }

    // ----- Oracle self-checks (executable mirrors of the Lean laws) --------------------

    [Fact]
    public void Oracle_SatisfiesTheCoreAlgebraLawsOnTheCatalog()
    {
        foreach (var shape in ArityDifferentialMatrix.Shapes)
        {
            var value = shape.Value;

            // normalize_idempotent: catalog values are stored canonical values.
            Assert.Equal(value.Neutral, AlgebraOracle.Normalize(value).Neutral);

            // capture_singleton: capture [v] = normalize v.
            Assert.Equal(AlgebraOracle.Normalize(value).Neutral, AlgebraOracle.Capture([value]).Neutral);

            // items_collect: spread ∘ collect = id on supplies.
            var items = AlgebraOracle.Items(value);
            Assert.Equal(
                string.Join("|", items.Select(i => i.Neutral)),
                string.Join("|", AlgebraOracle.Items(AlgebraOracle.Collect(items)).Select(i => i.Neutral)));

            // collect_singleton_ne_item: a singleton collected segment is never erased.
            Assert.NotEqual(value.Neutral, AlgebraOracle.Collect([value]).Neutral);

            // openLoneStructure_singleton: deconstruction's one-value opening is the item view.
            Assert.Equal(
                string.Join("|", items.Select(i => i.Neutral)),
                string.Join("|", AlgebraOracle.OpenLoneStructure([value]).Select(i => i.Neutral)));

            // repeated_spread_fixed_iff: the fixed point holds exactly on
            // non-singleton first spreads or a lone atom item.
            var repeated = AlgebraOracle.SpreadSupply(value, 2);
            var isFixedPoint =
                string.Join("|", repeated.Select(i => i.Neutral)) == string.Join("|", items.Select(i => i.Neutral));
            var lawPredicts = items.Count != 1 || items[0] is OracleVal.AtomVal;
            Assert.True(isFixedPoint == lawPredicts,
                $"repeated_spread_fixed_iff violated by the oracle itself on {shape.Id}");
        }

        // valueCount: only the empty sequence value is invisible.
        Assert.Equal(0, AlgebraOracle.ValueCount(OracleVal.Seq()));
        Assert.Equal(1, AlgebraOracle.ValueCount(OracleVal.List()));
        Assert.Equal(1, AlgebraOracle.ValueCount(OracleVal.Atom(7)));

        // capture_items_of_list: spread-then-capture converts a list to the sequence world.
        Assert.Equal("S[1, 2]", AlgebraOracle.Capture(AlgebraOracle.Items(OracleVal.List(OracleVal.Atom(1), OracleVal.Atom(2)))).Neutral);
    }

    // ----- Schema, determinism, and coverage accounting --------------------------------

    [Fact]
    public void Schema_IdsAreUniqueKebabCaseAndDisjointFromOtherCorpora()
    {
        var idPattern = new Regex("^[a-z0-9]+([-~][a-z0-9]+)*$");
        var seen = new HashSet<string>(StringComparer.Ordinal);
        foreach (var id in Matrix.Select(c => c.Id)
                     .Concat(Relational.Select(c => c.Id))
                     .Concat(Diagnostics.Select(c => c.Id)))
        {
            Assert.True(idPattern.IsMatch(id.Replace("--", "-")), $"'{id}' is not a stable kebab-style id.");
            Assert.True(seen.Add(id), $"Duplicate case id '{id}'.");
        }

        var explorerIds = SemanticExplorerCorpus.AllCases().Select(c => c.Id)
            .Concat(LanguageSpec.LanguageSpecCorpus.AllCases().Select(c => c.Id))
            .ToHashSet(StringComparer.Ordinal);
        foreach (var id in seen)
            Assert.False(explorerIds.Contains(id), $"Case id '{id}' collides with another corpus.");
    }

    [Fact]
    public void Generation_IsDeterministicAcrossCleanRegenerations()
    {
        var first = ArityDifferentialMatrix.GenerateFresh();
        var second = ArityDifferentialMatrix.GenerateFresh();

        static string Fingerprint(
            (IReadOnlyList<DifferentialCase> Matrix, IReadOnlyList<ExcludedCombination> Excluded,
                IReadOnlyList<RelationalCase> Relational, IReadOnlyList<DiagnosticCase> Diagnostics) generated)
        {
            var text = new StringBuilder();
            foreach (var c in generated.Matrix)
                text.AppendLine($"{c.Id}{c.Source}{c.Expected.Neutral}{c.PrimaryLaw}{string.Join(";", c.AlgebraTrace)}");
            foreach (var e in generated.Excluded)
                text.AppendLine($"{e.Receiver}|{e.Form}|{e.ShapeId}|{e.Multiplicity}{e.Reason}");
            foreach (var r in generated.Relational)
                text.AppendLine($"{r.Id}{r.LeftSource}{r.RightSource}{r.ExpectAgreement}{r.ExpectedLeft.Neutral}{r.ExpectedRight.Neutral}");
            foreach (var d in generated.Diagnostics)
                text.AppendLine($"{d.Id}{d.Source}{d.ExpectedParseDiagnosticFragment}{d.ExpectedErrorCategory}");
            return text.ToString();
        }

        Assert.Equal(Fingerprint(first), Fingerprint(second));
        Assert.Equal(Fingerprint(first), Fingerprint((Matrix, ArityDifferentialMatrix.ExcludedCells(), Relational, Diagnostics)));
    }

    [Fact]
    public void Coverage_EveryTheoreticalCellIsCoveredOrExcludedWithAReason()
    {
        // Touching ExcludedCells() forces the generator's own completeness
        // check: an uncovered cell without a matching exclusion rule throws.
        var excluded = ArityDifferentialMatrix.ExcludedCells();
        var coveredCells = Matrix
            .Select(c => (c.Receiver, c.Form, c.ShapeId, c.Multiplicity))
            .Distinct()
            .ToList();

        Assert.Equal(ArityDifferentialMatrix.TheoreticalCellCount, coveredCells.Count + excluded.Count);

        // Every receiver, shape, multiplicity, and form is genuinely reached.
        foreach (var receiver in Enum.GetValues<ReceiverKind>())
            Assert.Contains(coveredCells, cell => cell.Receiver == receiver);
        foreach (var form in Enum.GetValues<BindingForm>())
            Assert.Contains(coveredCells, cell => cell.Form == form);
        foreach (var shape in ArityDifferentialMatrix.Shapes)
            Assert.Contains(coveredCells, cell => cell.ShapeId == shape.Id);
        foreach (var multiplicity in Enum.GetValues<SpreadMultiplicity>())
            Assert.Contains(coveredCells, cell => cell.Multiplicity == multiplicity);

        // Every law in the taxonomy has a Lean reference, and every law is
        // exercised by at least one generated case.
        var usedLaws = Matrix.Select(c => c.PrimaryLaw)
            .Concat(Relational.Select(c => c.PrimaryLaw))
            .Concat(Diagnostics.Select(c => c.PrimaryLaw))
            .ToHashSet();
        foreach (var law in Enum.GetValues<ReceiverLaw>())
        {
            Assert.True(ReceiverLaws.LeanReference.ContainsKey(law), $"{law} has no Lean reference.");
            Assert.True(usedLaws.Contains(law), $"{law} is declared but never exercised by a generated case.");
        }

        WriteCoverageReport(coveredCells.Count, excluded);
    }

    private static void WriteCoverageReport(int coveredCellCount, IReadOnlyList<ExcludedCombination> excluded)
    {
        var report = new
        {
            corpus = "ArityDifferentialMatrix",
            theoreticalCells = ArityDifferentialMatrix.TheoreticalCellCount,
            coveredCells = coveredCellCount,
            excludedCells = excluded.Count,
            executableMatrixCases = Matrix.Count,
            relationalCases = Relational.Count,
            diagnosticCases = Diagnostics.Count,
            exclusionsByReason = excluded.GroupBy(e => e.Reason)
                .OrderByDescending(g => g.Count())
                .Select(g => new { reason = g.Key, cells = g.Count() }),
            casesByReceiver = Tally(Matrix.Select(c => c.Receiver.ToString())),
            casesByShape = Tally(Matrix.Select(c => c.ShapeId)),
            casesByMultiplicity = Tally(Matrix.Select(c => c.Multiplicity.ToString())),
            casesByPrimaryLaw = Tally(Matrix.Select(c => c.PrimaryLaw.ToString())
                .Concat(Relational.Select(c => c.PrimaryLaw.ToString()))
                .Concat(Diagnostics.Select(c => c.PrimaryLaw.ToString()))),
            relationalByFamily = Tally(Relational.Select(c => c.Family)),
            diagnosticsByFamily = Tally(Diagnostics.Select(c => c.Family)),
        };

        var path = Path.Combine(AppContext.BaseDirectory, "ArityDifferentialReport.json");
        File.WriteAllText(path, JsonSerializer.Serialize(report, new JsonSerializerOptions { WriteIndented = true }));
    }

    private static SortedDictionary<string, int> Tally(IEnumerable<string> keys)
    {
        var tally = new SortedDictionary<string, int>(StringComparer.Ordinal);
        foreach (var key in keys)
            tally[key] = tally.TryGetValue(key, out var count) ? count + 1 : 1;
        return tally;
    }

    [Fact]
    public void Coverage_PinnedPartitionCounts()
    {
        // Pinned so a silent matrix shrink (a template or shape dropping out)
        // is a reviewed diff, not an accident. Update deliberately when the
        // catalog or template set changes.
        Assert.Equal(14, ArityDifferentialMatrix.Shapes.Count);
        Assert.Equal(756, ArityDifferentialMatrix.TheoreticalCellCount);
    }
}
