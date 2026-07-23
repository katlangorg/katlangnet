using KatLang.ParserFuzz;

namespace KatLang.Tests;

/// <summary>
/// Phase 7 readiness: a deterministic stratified sample of the editor parameter space reaches every
/// template, surface, cursor kind, edit kind, execution mode and line-ending mode, and every point
/// runs the full harness — build, model invariants, surface, determinism, edit, and relations —
/// without an unexpected exception. "The campaign covered X" is therefore a measured claim rather
/// than an assumption, and the whole space is proven to stay inside fixed bounds.
/// </summary>
public class EditorReadinessTests
{
    private static List<EditorParameters> Stratified { get; } = EditorSpace.EnumerateStratified().ToList();

    [Fact]
    public void TheStratifiedSpace_ReachesEveryTemplateSurfaceCursorEditAndMode()
    {
        Assert.Equal(EditorTables.TemplateCount, Stratified.Select(p => p.Template).Distinct().Count());
        Assert.Equal(EditorTables.SurfaceCount, Stratified.Select(p => p.Surface).Distinct().Count());
        Assert.Equal(EditorTables.CursorCount, Stratified.Select(p => p.Cursor).Distinct().Count());
        Assert.Equal(EditorTables.EditCount, Stratified.Select(p => p.Edit).Distinct().Count());
        Assert.Equal(EditorTables.ExecutionCount, Stratified.Select(p => p.ExecutionMode).Distinct().Count());
        Assert.Equal(EditorTables.LineEndingCount, Stratified.Select(p => p.LineEndings).Distinct().Count());
        Assert.Equal(EditorTables.PlacementCount, Stratified.Select(p => p.Placement).Distinct().Count());
        Assert.Equal(EditorTables.GroupCount, Stratified.Select(p => p.InjectionGroup).Distinct().Count());
    }

    [Fact]
    public void EveryStratifiedPoint_RunsTheWholeHarnessWithoutAnUnexpectedException()
    {
        var outcomes = new SortedSet<string>(StringComparer.Ordinal);
        var relations = new SortedSet<string>(StringComparer.Ordinal);
        var declines = 0;
        var built = 0;

        foreach (var parameters in Stratified)
        {
            EditorReport report;
            try
            {
                report = EditorInvariants.Run(parameters.Encode());
            }
            catch (Exception exception)
            {
                Assert.Fail(
                    $"Editor harness threw on {parameters}:\n  {exception.GetType().Name}: {exception.Message}");
                return;
            }

            Assert.NotNull(report.Fingerprint);
            Assert.True(
                report.Case.SourceCodeUnits.Length <= EditorTables.MaxSourceCodeUnits,
                $"{parameters} built a source over the code-unit cap.");
            Assert.True(
                report.Case.EditedCodeUnits.Length <= EditorTables.MaxSourceCodeUnits,
                $"{parameters} built an edited source over the code-unit cap.");

            outcomes.Add(report.Observation.Outcome.ToString());
            foreach (var relation in report.Relations.Checked) relations.Add(relation);
            if (report.Observation.Outcome == EditorToolingOutcome.Built) built++;
            else declines++;
        }

        // Both outcomes are reached: models are built, and the unresolved-load decline path fires.
        Assert.True(built > 0, "No stratified point built a semantic model.");
        Assert.True(declines > 0, "The unresolved-load decline path was never reached.");

        // Every metamorphic relation ran on at least one point, or its coverage claim is empty.
        Assert.Contains(EditorRelations.WhitespaceNeutral, relations);
        Assert.Contains(EditorRelations.LineEndingNeutral, relations);
        Assert.Contains(EditorRelations.Rename, relations);
        Assert.Contains(EditorRelations.UnrelatedDeclaration, relations);
        Assert.Contains(EditorRelations.DottedOrdinary, relations);
    }

    [Fact]
    public void EveryStratifiedPoint_ProducesAStableFingerprint()
    {
        foreach (var parameters in Stratified)
        {
            var payload = parameters.Encode();
            var first = EditorInvariants.Run(payload);
            var second = EditorInvariants.Run(payload);
            Assert.Equal(first.Fingerprint, second.Fingerprint);
            Assert.Equal(first.Case.HexUnits, second.Case.HexUnits);
            Assert.Equal(first.Case.EditedHexUnits, second.Case.EditedHexUnits);
        }
    }

    [Fact]
    public void Fingerprints_CarryNothingThatCouldDifferBetweenRuns()
    {
        string[] forbidden =
        [
            "threadid", "managedthread", "processid", "elapsed", "ticks", "hashcode", "@0x", "system.", "\n",
        ];

        foreach (var parameters in Stratified)
        {
            var report = EditorInvariants.Run(parameters.Encode());
            var lowered = report.Fingerprint.ToLowerInvariant();
            foreach (var token in forbidden)
                Assert.False(
                    lowered.Contains(token, StringComparison.Ordinal),
                    $"Fingerprint for {parameters} contains unstable token '{token}':\n  {report.Fingerprint}");

            // The fingerprint must not embed the generated program text.
            foreach (var line in report.Case.Source.Split('\n'))
                if (line.Length >= 8)
                    Assert.DoesNotContain(line, report.Fingerprint, StringComparison.Ordinal);
        }
    }

    [Fact]
    public void EveryDecodedPoint_StaysInsideFixedStructuralBounds()
    {
        foreach (var parameters in Stratified)
        {
            Assert.True(parameters.Encode().Length <= EditorDecoder.MaxPayloadPrefixBytes);
            Assert.Equal(parameters, EditorDecoder.Decode(parameters.Encode()));
            Assert.Equal(parameters, EditorDecoder.Normalize(parameters));
        }
    }
}
