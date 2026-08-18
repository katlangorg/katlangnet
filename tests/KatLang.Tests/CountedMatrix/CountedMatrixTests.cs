using System.Text;

namespace KatLang.Tests.CountedMatrix;

/// <summary>
/// Runner for the counted-only known-answer matrix
/// (<see cref="CountedMatrixCorpus"/>). Every case executes through the
/// production front end and BOTH evaluators
/// (<see cref="SemanticExplorerHarness.Observe(string, string)"/> cross-checks
/// Evaluator.RunCounted, Evaluator.Run, and KatLangEngine.Run), and the
/// observed root emitted count plus structural cardinality is compared against
/// the case's hand-written expected answer. The coverage meta-tests make
/// missing 0/1/2/N rows a FAILING test, so "which consumers have explicit
/// cardinality coverage" is answered by the <see cref="CountedConsumer"/> enum
/// plus a green run.
/// </summary>
public class CountedMatrixTests
{
    private static readonly IReadOnlyList<CountedMatrixCase> Matrix = CountedMatrixCorpus.Cases();

    private static readonly IReadOnlyDictionary<string, CountedMatrixCase> ById =
        Matrix.ToDictionary(c => c.Id, StringComparer.Ordinal);

    // Each program is observed at most once per test session.
    private static readonly Lazy<IReadOnlyDictionary<string, ExplorerObservation>> Observations =
        new(
            () => Matrix.ToDictionary(
                c => c.Id,
                c => SemanticExplorerHarness.Observe(c.Id, c.Source),
                StringComparer.Ordinal),
            LazyThreadSafetyMode.ExecutionAndPublication);

    public static TheoryData<string> CaseIds()
    {
        var data = new TheoryData<string>();
        foreach (var matrixCase in Matrix)
            data.Add(matrixCase.Id);
        return data;
    }

    [Theory]
    [MemberData(nameof(CaseIds))]
    public void Matrix_CardinalityMatchesKnownAnswer(string caseId)
    {
        var matrixCase = ById[caseId];
        var observation = Observations.Value[caseId];

        if (observation.Outcome == "parseError")
        {
            var diagnostics = Parser.Parse(matrixCase.Source).Diagnostics;
            Assert.Fail(Report(matrixCase, observation,
                "the source must parse cleanly, but the front end reported:"
                + Environment.NewLine
                + string.Join(Environment.NewLine, diagnostics.Select(d => "    - " + d.Message.Split('\n')[0]))));
        }

        if (matrixCase.ExpectedErrorCategory is { } expectedCategory)
        {
            if (observation.Outcome != "err")
                Assert.Fail(Report(matrixCase, observation,
                    $"expected evaluation error '{expectedCategory}' but the program evaluated"));
            if (observation.ErrorCategory != expectedCategory)
                Assert.Fail(Report(matrixCase, observation,
                    $"expected error category '{expectedCategory}' but observed '{observation.ErrorCategory}'"));
            return;
        }

        if (observation.Outcome != "ok")
            Assert.Fail(Report(matrixCase, observation,
                $"expected a value but evaluation failed with '{observation.ErrorCategory}'"));

        if (matrixCase.ExpectedRaw is { } expectedRaw && observation.Raw != expectedRaw)
            Assert.Fail(Report(matrixCase, observation,
                $"raw structure mismatch: expected {expectedRaw}, observed {observation.Raw}"));

        if (matrixCase.ExpectedShape is { } expectedShape)
        {
            var observedShape = CountedMatrixCase.ShapeOf(observation.Value!);
            if (observedShape != expectedShape)
                Assert.Fail(Report(matrixCase, observation,
                    $"structural cardinality mismatch: expected {expectedShape}, observed {observedShape}"));
        }

        if (observation.Emitted != matrixCase.ExpectedEmitted)
            Assert.Fail(Report(matrixCase, observation,
                $"emitted-count mismatch: expected n={matrixCase.ExpectedEmitted}, observed n={observation.Emitted}"
                + " — a value-boundary / supply-count divergence"));
    }

    private static string Report(
        CountedMatrixCase matrixCase, ExplorerObservation observation, string difference)
    {
        var report = new StringBuilder();
        report.AppendLine($"COUNTED-MATRIX MISMATCH: {matrixCase.Id}");
        report.AppendLine($"  consumer={matrixCase.Consumer} cardinality={matrixCase.Cardinality} form={matrixCase.Form}");
        report.AppendLine($"  rule: {matrixCase.Rule}");
        report.AppendLine("  source:");
        foreach (var line in matrixCase.Source.Split('\n'))
            report.AppendLine($"    | {line}");
        report.AppendLine($"  expected: {DescribeExpectation(matrixCase)}");
        report.AppendLine($"  actual:   {DescribeObservation(observation)}");
        report.AppendLine($"  difference: {difference}");
        return report.ToString();
    }

    private static string DescribeExpectation(CountedMatrixCase matrixCase) => matrixCase switch
    {
        { ExpectedErrorCategory: { } category } => $"err {category}",
        { ExpectedRaw: { } raw } => $"ok raw={raw} n={matrixCase.ExpectedEmitted}",
        _ => $"ok shape={matrixCase.ExpectedShape} n={matrixCase.ExpectedEmitted}",
    };

    private static string DescribeObservation(ExplorerObservation observation) => observation.Outcome switch
    {
        "ok" =>
            $"ok raw={observation.Raw} shape={CountedMatrixCase.ShapeOf(observation.Value!)} n={observation.Emitted}",
        "err" => $"err {observation.ErrorCategory}",
        _ => "parseError",
    };

    // ----- Host flattening boundary -------------------------------------------------

    public static TheoryData<string> HostFlatCaseIds()
    {
        var data = new TheoryData<string>();
        foreach (var hostCase in CountedMatrixCorpus.HostFlatCases())
            data.Add(hostCase.Id);
        return data;
    }

    [Theory]
    [MemberData(nameof(HostFlatCaseIds))]
    public void HostFlatBoundary_AtomCountMatchesKnownAnswer(string caseId)
    {
        var hostCase = CountedMatrixCorpus.HostFlatCases().Single(c => c.Id == caseId);
        var root = SourceProvenance.ParseValid(hostCase.Source).Root;
        var flat = Evaluator.RunFlat(new Expr.AlgorithmExpr(root));

        Assert.True(flat.IsOk,
            $"{hostCase.Id}: RunFlat failed: {(flat.IsError ? flat.Error.ToString() : "")}");
        Assert.True(flat.Value.Count == hostCase.ExpectedAtomCount,
            $"{hostCase.Id}: expected {hostCase.ExpectedAtomCount} host atoms but observed "
            + $"{flat.Value.Count} ([{string.Join(", ", flat.Value)}]) — rule: {hostCase.Rule}");
    }

    [Fact]
    public void HostFlatBoundary_HasExplicitCardinalityCoverage()
    {
        var covered = CountedMatrixCorpus.HostFlatCases().Select(c => c.Cardinality).ToHashSet();
        var missing = new[]
            {
                ProducerCardinality.Zero,
                ProducerCardinality.One,
                ProducerCardinality.Two,
                ProducerCardinality.Many,
            }
            .Where(cardinality => !covered.Contains(cardinality))
            .ToList();
        Assert.True(missing.Count == 0,
            "Host flattening boundary missing cardinality rows: " + string.Join(", ", missing));
    }

    // ----- Corpus integrity and coverage ------------------------------------------

    [Fact]
    public void CaseIds_AreUnique()
    {
        var duplicates = Matrix
            .GroupBy(c => c.Id, StringComparer.Ordinal)
            .Where(g => g.Count() > 1)
            .Select(g => g.Key)
            .ToList();
        Assert.True(duplicates.Count == 0, "Duplicate case ids: " + string.Join(", ", duplicates));
    }

    [Fact]
    public void EveryCase_HasExactlyOneExpectationForm()
    {
        var malformed = new List<string>();
        foreach (var matrixCase in Matrix)
        {
            var isError = matrixCase.ExpectedErrorCategory is not null;
            var isRaw = matrixCase.ExpectedRaw is not null;
            var isShape = matrixCase.ExpectedShape is not null;
            var formCount = (isError ? 1 : 0) + (isRaw ? 1 : 0) + (isShape ? 1 : 0);
            if (formCount != 1)
                malformed.Add($"{matrixCase.Id} (forms set: {formCount})");
            if (!isError && matrixCase.ExpectedEmitted is null)
                malformed.Add($"{matrixCase.Id} (value expectation without emitted count)");
        }

        Assert.True(malformed.Count == 0, "Malformed expectations: " + string.Join(", ", malformed));
    }

    /// <summary>
    /// The matrix contract: EVERY consumer in <see cref="CountedConsumer"/> has
    /// explicit producer-cardinality coverage for 0, 1, 2, and N outputs.
    /// Adding a consumer to the enum without its rows fails here — the corpus
    /// is the required place to add them.
    /// </summary>
    [Fact]
    public void EveryConsumer_HasExplicitCardinalityCoverage()
    {
        var required = new[]
        {
            ProducerCardinality.Zero,
            ProducerCardinality.One,
            ProducerCardinality.Two,
            ProducerCardinality.Many,
        };

        var missing = new List<string>();
        foreach (var consumer in Enum.GetValues<CountedConsumer>())
        {
            var covered = Matrix
                .Where(c => c.Consumer == consumer)
                .Select(c => c.Cardinality)
                .ToHashSet();
            foreach (var cardinality in required)
            {
                if (!covered.Contains(cardinality))
                    missing.Add($"{consumer}/{cardinality}");
            }
        }

        Assert.True(missing.Count == 0,
            "Consumers missing required cardinality rows (add them to CountedMatrixCorpus): "
            + string.Join(", ", missing));
    }

    /// <summary>
    /// Consumers where direct multi-output consumption and capture-boundary
    /// consumption are both legal must show the contrast explicitly.
    /// </summary>
    [Fact]
    public void CaptureContrastConsumers_HaveCaptureWrappedCases()
    {
        var missing = CountedMatrixCorpus.CaptureContrastConsumers
            .Where(consumer => !Matrix.Any(
                c => c.Consumer == consumer && c.Form == SupplyForm.CaptureWrapped))
            .Select(consumer => consumer.ToString())
            .ToList();

        Assert.True(missing.Count == 0,
            "Capture-contrast consumers without a CaptureWrapped case: " + string.Join(", ", missing));
    }
}
