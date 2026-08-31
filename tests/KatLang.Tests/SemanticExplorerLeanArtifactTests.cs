using System.Text;

namespace KatLang.Tests;

/// <summary>
/// Generates and pins <c>lean/SemanticExplorerCases.lean</c>: the Lean/C#
/// differential half of the semantic explorer. Every Lean-representable
/// corpus case is emitted as a Lean AST construction plus a <c>#guard</c>
/// pinning the neutral observation the C# evaluator produced. If C# behavior
/// changes, this test fails (regenerate and review the diff); if Lean behavior
/// diverges from the recorded observation, <c>lake build SemanticExplorerCases</c>
/// fails on the guard. Together they keep the two implementations observably
/// aligned on the whole corpus.
///
/// Regenerate with:
///   $env:KATLANG_REGENERATE_SEMANTIC_EXPLORER = "1"
///   dotnet test --filter SemanticExplorerLeanArtifact
/// </summary>
public class SemanticExplorerLeanArtifactTests
{
    private const string RegenerateVariable = "KATLANG_REGENERATE_SEMANTIC_EXPLORER";

    [Fact]
    public void CachedCorpusObjectGraphs_ExposeNoMutableCollectionViews()
    {
        static void AssertReadOnly<T>(IReadOnlyList<T> values, string path)
        {
            Assert.False(
                values is System.Collections.IList { IsReadOnly: false },
                $"{path} exposes a mutable non-generic IList view.");
            Assert.False(
                values is IList<T> { IsReadOnly: false },
                $"{path} exposes a mutable generic IList view.");
        }

        static void InspectExplorerValue(ExplorerValue value, string path)
        {
            switch (value)
            {
                case ExplorerValue.Seq(var items):
                    AssertReadOnly(items, path);
                    for (var i = 0; i < items.Count; i++)
                        InspectExplorerValue(items[i], $"{path}[{i}]");
                    break;
                case ExplorerValue.ListOf(var items):
                    AssertReadOnly(items, path);
                    for (var i = 0; i < items.Count; i++)
                        InspectExplorerValue(items[i], $"{path}[{i}]");
                    break;
                case ExplorerValue.Wrap(var inner):
                    InspectExplorerValue(inner, path + ".Inner");
                    break;
                case ExplorerValue.Empty or ExplorerValue.Num:
                    break;
                default:
                    throw new InvalidOperationException(
                        $"Unhandled explorer value variant {value.GetType().Name}.");
            }
        }

        AssertReadOnly(SemanticExplorerCorpus.Values, nameof(SemanticExplorerCorpus.Values));
        foreach (var (id, value) in SemanticExplorerCorpus.Values)
            InspectExplorerValue(value, $"Values[{id}]");

        AssertReadOnly(SemanticExplorerCorpus.AllCases(), "SemanticExplorerCorpus.AllCases()");
        var languageSpec = LanguageSpec.LanguageSpecCorpus.AllCases();
        AssertReadOnly(languageSpec, "LanguageSpecCorpus.AllCases()");
        foreach (var specCase in languageSpec)
            AssertReadOnly(specCase.Probes, $"LanguageSpec[{specCase.Id}].Probes");
    }
    private const string ArtifactRelativePath = "lean/SemanticExplorerCases.lean";

    [Fact]
    public void GeneratedLeanArtifact_MatchesCurrentCSharpObservations()
    {
        var expected = GenerateArtifact();
        var path = Path.Combine(FindRepoRoot(), ArtifactRelativePath);

        if (Environment.GetEnvironmentVariable(RegenerateVariable) == "1")
        {
            File.WriteAllText(path, expected);
            return;
        }

        Assert.True(File.Exists(path),
            $"{ArtifactRelativePath} is missing. Set {RegenerateVariable}=1 and rerun this test to generate it.");

        var actual = File.ReadAllText(path).ReplaceLineEndings("\n");
        Assert.True(expected == actual,
            $"{ArtifactRelativePath} is out of date with current C# evaluator observations. " +
            $"Set {RegenerateVariable}=1, rerun this test, review the diff, and run " +
            "`lake build SemanticExplorerCases` to check the Lean side. " +
            DescribeFirstDifference(expected, actual));
    }

    /// <summary>
    /// The generated artifact never contains an observation the C# harness
    /// could not classify (exceptions or unintended parse errors on
    /// Lean-representable cases would silently shrink differential coverage).
    /// </summary>
    [Fact]
    public void LeanRepresentableCases_AllProduceComparableObservations()
    {
        foreach (var explorerCase in SemanticExplorerCorpus.AllCases().Where(c => c.LeanProgram is not null))
        {
            var observation = SemanticExplorerHarness.Observe(explorerCase);
            Assert.True(observation.Outcome is "ok" or "err",
                $"{explorerCase.Id} is marked Lean-representable but observed '{observation.Outcome}'.");
        }
    }

    /// <summary>
    /// Pins the corpus partition: the surface corpus splits exactly into
    /// Lean-representable differential cases and C#-parse-level cases (Lean
    /// has no surface parser, so a case is excluded from the artifact iff it
    /// is a deliberate parse-error probe). This keeps the accounting table in
    /// docs/design/sequence-boundary-audit-2026-07.md from drifting: the
    /// artifact guard total is always surfaceCases - parseLevelCases plus the
    /// internal-node cases.
    /// </summary>
    [Fact]
    public void CorpusPartition_LeanExclusionsAreExactlyTheParseLevelCases()
    {
        var allCases = SemanticExplorerCorpus.AllCases();

        foreach (var explorerCase in allCases)
        {
            var isParseError = SemanticExplorerHarness.Observe(explorerCase).Outcome == "parseError";
            Assert.True((explorerCase.LeanProgram is null) == (explorerCase.LeanExclusionReason is not null),
                $"{explorerCase.Id}: LeanProgram and LeanExclusionReason must form an exact derived/excluded partition.");
            if (explorerCase.LeanExclusionReason is { } reason)
            {
                Assert.False(string.IsNullOrWhiteSpace(reason),
                    $"{explorerCase.Id}: a Lean exclusion requires a non-blank reviewed reason.");
            }

            Assert.True((explorerCase.LeanProgram is null) == isParseError,
                $"{explorerCase.Id}: LeanProgram is {(explorerCase.LeanProgram is null ? "null" : "set")} " +
                $"but the case {(isParseError ? "is" : "is not")} a parse-error case; " +
                "Lean exclusion and parse-level status must coincide.");
        }

        var excluded = allCases.Where(c => c.LeanProgram is null).Select(c => c.Id)
            .OrderBy(id => id, StringComparer.Ordinal)
            .ToList();
        var expected = SemanticExplorerCorpus.Values.Select(v => $"indexNeg__{v.Id}")
            .Concat(
            [
                "special__semicolonSeparator",
                "special__spreadAsBinaryOperand",
                "special__trailingComma",
                "special__listUnterminated",
                "special__listDefinitionInside",
            ])
            .OrderBy(id => id, StringComparer.Ordinal)
            .ToList();
        Assert.Equal(expected, excluded);
    }

    /// <summary>
    /// M11 coverage ratchet. Every Lean-representable explorer case's program
    /// is derived from the source's real elaborated AST by
    /// <see cref="LeanAstEncoder"/> (same-program fidelity by construction);
    /// the C#-only remainder is exactly the deliberate parse-error probes
    /// (pinned by id in <see cref="CorpusPartition_LeanExclusionsAreExactlyTheParseLevelCases"/>).
    /// The pinned minimums may only be RAISED (or lowered in a reviewed diff
    /// that deliberately removes corpus cases). An encoder coverage regression
    /// cannot pass silently: a case that stops encoding fails corpus
    /// construction loudly, and a case reflagged C#-only both shrinks the
    /// count here and breaks the exclusion id list.
    /// </summary>
    [Fact]
    public void FidelityRatchet_EncoderDerivedCoverageCannotSilentlyShrink()
    {
        const int MinimumEncoderDerivedSurfaceCases = 1528;
        const int MinimumInternalNodeCases = 14;

        var allCases = SemanticExplorerCorpus.AllCases();
        var derived = allCases.Count(c => c.LeanProgram is not null);
        var csharpOnly = allCases.Count(c => c.LeanProgram is null);
        var internalNodes = SemanticExplorerCorpus.InternalNodeCases().Count;

        Assert.True(derived >= MinimumEncoderDerivedSurfaceCases,
            $"Encoder-derived fidelity coverage shrank below the pinned minimum {MinimumEncoderDerivedSurfaceCases}: "
            + $"{allCases.Count} surface cases = {derived} encoder-derived + {csharpOnly} deliberate parse-error probes. "
            + "Raise the pin only in a reviewed diff that adds cases; a shrink means a case silently left the "
            + "differential corpus.");
        Assert.Equal(allCases.Count, derived + csharpOnly);
        Assert.True(internalNodes >= MinimumInternalNodeCases,
            $"Internal-node differential coverage shrank below the pinned minimum {MinimumInternalNodeCases} "
            + $"(actual {internalNodes}).");
    }

    [Fact]
    public void SequenceBoundaryAudit_AccountingMatchesCurrentCorpus()
    {
        static string Count(int value) => value.ToString("N0", System.Globalization.CultureInfo.InvariantCulture);

        var allCases = SemanticExplorerCorpus.AllCases();
        var observations = allCases.Select(SemanticExplorerHarness.Observe).ToList();
        var surface = allCases.Count;
        var templateCases = allCases.Where(c => !c.Id.StartsWith("special__", StringComparison.Ordinal)).ToList();
        var templates = templateCases.Count;
        var templateIds = templateCases.Select(c => c.TemplateId).Distinct().Count();
        var valueIds = templateCases.Select(c => c.ValueId).Distinct().Count();
        var specials = surface - templates;
        var leanRepresentable = allCases.Count(c => c.LeanProgram is not null);
        var internalNodes = SemanticExplorerCorpus.InternalNodeCases().Count;
        var outcomes = observations.GroupBy(o => o.Outcome).ToDictionary(g => g.Key, g => g.Count());

        var path = Path.Combine(FindRepoRoot(), "docs/design/sequence-boundary-audit-2026-07.md");
        var document = File.ReadAllText(path).ReplaceLineEndings("\n");

        Assert.Contains($"all {Count(surface)} surface cases", document, StringComparison.Ordinal);
        Assert.Contains($"(**{Count(leanRepresentable)} surface cases**", document, StringComparison.Ordinal);
        var expectedSurfaceRow =
            $"| Surface corpus (= C# semantic report surface section) | {Count(surface)} | " +
            $"{Count(templates)} template cases ({templateIds} receiver templates x {valueIds} values) + {specials} specials; " +
            $"outcomes {Count(outcomes["ok"])} ok / {Count(outcomes["err"])} err / " +
            $"{Count(outcomes["parseError"])} parse-error |";
        Assert.True(
            document.Contains(expectedSurfaceRow, StringComparison.Ordinal),
            $"Sequence-boundary audit is missing expected row:{Environment.NewLine}{expectedSurfaceRow}");
        Assert.Contains(
            $"| Generated Lean case guards | {Count(leanRepresentable + internalNodes)} | " +
            $"{Count(leanRepresentable)} surface + {internalNodes} internal-node",
            document,
            StringComparison.Ordinal);
    }

    internal static string GenerateArtifact()
    {
        var allCases = SemanticExplorerCorpus.AllCases();
        var expectedSurface = allCases.Count(c => c.LeanProgram is not null);
        var expectedInternal = SemanticExplorerCorpus.InternalNodeCases().Count;

        var builder = new StringBuilder();
        builder.Append($"""
            import KatLang

            /-!
            GENERATED FILE - DO NOT EDIT BY HAND.

            Differential corpus for the small-state semantic explorer
            (tests/KatLang.Tests/SemanticExplorerCorpus.cs). Each case is the Lean AST
            construction equivalent to a KatLang source program, and each `#guard` pins
            the neutral observation recorded from the C# evaluator. A failing guard is a
            Lean/C# divergence on that case.

            Partition (machine-checked by the `*CaseIds.length` guards below):
            - surface corpus cases: {allCases.Count}
            - excluded parse-level cases (Lean has no surface parser): {allCases.Count - expectedSurface}
            - Lean-representable surface cases: {expectedSurface}
            - internal-node cases: {expectedInternal}
            - total generated guards: {expectedSurface + expectedInternal} case guards + 2 count guards

            Regenerate from the repo root with:
              $env:KATLANG_REGENERATE_SEMANTIC_EXPLORER = "1"
              dotnet test .\KatLang.slnx --filter SemanticExplorerLeanArtifact
            -/

            namespace SemanticExplorerCases
            open KatLang

            """.ReplaceLineEndings("\n"));
        builder.Append('\n');
        builder.Append(LeanObsTemplate.SharedDefinitions.ReplaceLineEndings("\n"));
        builder.Append("\n\n");

        var surfaceIds = new List<string>();
        foreach (var explorerCase in allCases)
        {
            if (explorerCase.LeanProgram is null)
                continue;

            var observation = SemanticExplorerHarness.Observe(explorerCase);
            if (observation.Outcome is not ("ok" or "err"))
            {
                throw new InvalidOperationException(
                    $"{explorerCase.Id} is Lean-representable but observed '{observation.Outcome}'; refusing to silently shrink the differential corpus.");
            }

            var sourceComment = explorerCase.Source.Replace("\n", " \\n ");
            builder.Append($"-- {explorerCase.Id}: {sourceComment}\n");
            builder.Append($"def case_{explorerCase.Id} : Expr :=\n  {explorerCase.LeanProgram}\n");
            builder.Append($"#guard obs case_{explorerCase.Id} == \"{observation.Neutral}\"\n\n");
            surfaceIds.Add(explorerCase.Id);
        }

        builder.Append($"-- {surfaceIds.Count} differential cases.\n\n");

        AppendCountGuard(builder, "surfaceCaseIds", surfaceIds, expectedSurface,
            "Machine-checked surface partition count: the id list is built by the same\n" +
            "loop that emits the guards above, while the expected total is computed\n" +
            "independently from the corpus partition, so a generation bug fails `lake build`.");

        builder.Append("""
            /-!
            Direct internal-node cases: `Expr.sequenceConstruct` is an INTERNAL node —
            the surface parser never produces it and its value evaluation drops `()`
            leaves, unlike written parentheses. These cases pin that internal behavior
            against the C# evaluator's observations of the same hand-constructed ASTs
            (see tests/KatLang.Tests/SequenceConstructContainmentTests.cs and
            SemanticExplorerCorpus.InternalNodeCases).
            -/

            """.ReplaceLineEndings("\n"));

        var internalIds = new List<string>();
        foreach (var internalCase in SemanticExplorerCorpus.InternalNodeCases())
        {
            // The Lean text is derived from the SAME constructed AST the C#
            // observation runs on (ObserveAst wraps the root output in an
            // identical one-slot root algorithm), so the two sides cannot
            // encode different programs (LeanAstEncoder covers
            // Expr.SequenceConstruct for exactly this purpose).
            var rootOutput = internalCase.RootOutput();
            var observation = SemanticExplorerHarness.ObserveAst(internalCase.Id, rootOutput);
            var root = new Algorithm.User(
                Parent: null, Parameters: [], Opens: [], Properties: [], Output: [rootOutput]);
            builder.Append($"-- internal__{internalCase.Id}: {internalCase.Description}\n");
            builder.Append($"def case_internal__{internalCase.Id} : Expr :=\n  {LeanAstEncoder.EncodeProgram(root)}\n");
            builder.Append($"#guard obs case_internal__{internalCase.Id} == \"{observation.Neutral}\"\n\n");
            internalIds.Add($"internal__{internalCase.Id}");
        }

        AppendCountGuard(builder, "internalNodeCaseIds", internalIds, expectedInternal,
            "Machine-checked internal-node partition count (see the surfaceCaseIds note).");

        builder.Append($"-- {internalIds.Count} internal-node cases.\n");
        builder.Append($"-- Total: {surfaceIds.Count + internalIds.Count} case guards ({surfaceIds.Count} surface + {internalIds.Count} internal-node).\n");
        builder.Append("end SemanticExplorerCases\n");
        return builder.ToString();
    }

    /// <summary>
    /// Emits a Lean id-list definition plus a <c>#guard</c> pinning its length
    /// to an independently computed partition count, so the artifact enforces
    /// its own accounting at <c>lake build</c> time instead of via comments.
    /// </summary>
    internal static void AppendCountGuard(
        StringBuilder builder, string listName, IReadOnlyList<string> ids, int expectedCount, string comment)
    {
        builder.Append("/--\n");
        builder.Append(comment);
        builder.Append("\n-/\n");
        builder.Append($"def {listName} : List String := [\n");
        builder.Append(string.Join(",\n", ids.Select(id => $"  \"{id}\"")));
        builder.Append("\n]\n");
        builder.Append($"#guard {listName}.length == {expectedCount}\n\n");
    }

    internal static string DescribeFirstDifference(string expected, string actual)
    {
        var expectedLines = expected.Split('\n');
        var actualLines = actual.Split('\n');
        var shared = Math.Min(expectedLines.Length, actualLines.Length);
        var lineIndex = 0;
        while (lineIndex < shared && expectedLines[lineIndex] == actualLines[lineIndex])
            lineIndex++;

        var context = "<no preceding case comment>";
        for (var i = Math.Min(lineIndex, expectedLines.Length - 1); i >= 0; i--)
        {
            if (expectedLines[i].StartsWith("-- ", StringComparison.Ordinal))
            {
                context = expectedLines[i];
                break;
            }
        }

        var expectedLine = lineIndex < expectedLines.Length ? expectedLines[lineIndex] : "<end of file>";
        var actualLine = lineIndex < actualLines.Length ? actualLines[lineIndex] : "<end of file>";
        return $"First mismatch at line {lineIndex + 1}, near {context}{Environment.NewLine}" +
            $"Expected: {expectedLine}{Environment.NewLine}Actual:   {actualLine}";
    }

    private static string FindRepoRoot()
    {
        var directory = AppContext.BaseDirectory;
        while (directory is not null && !File.Exists(Path.Combine(directory, "KatLang.slnx")))
            directory = Path.GetDirectoryName(directory);

        return directory
            ?? throw new InvalidOperationException("Could not locate repo root (KatLang.slnx) above test bin directory.");
    }
}
