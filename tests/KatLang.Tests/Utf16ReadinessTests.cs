using System.Collections.Immutable;
using System.Globalization;
using System.Text;
using KatLang.ParserFuzz;
using KatLang.Tests.LanguageSpec;

namespace KatLang.Tests;

/// <summary>
/// The independent pre-campaign audit for the UTF-16 target.
///
/// <para>These are the checks that make a clean campaign MEAN something. A fuzz target that
/// silently reaches only a corner of its space, or whose relations are vacuously true, or whose
/// fingerprint cannot distinguish two different outcomes, reports "no findings" just as loudly as
/// a correct one. Each test below removes one way of being fooled, and every bound the harness
/// enforces is justified here by MEASUREMENT over the deterministic stratified space rather than
/// by a number someone picked.</para>
///
/// <para>Set <c>KATLANG_UTF16_READINESS_REPORT</c> to a path to write the full distribution report,
/// following the repository's existing regenerate-artifact convention.</para>
/// </summary>
public class Utf16ReadinessTests
{
    private static readonly ImmutableArray<Utf16Parameters> Space = [.. Utf16Space.EnumerateStratified()];

    [Fact]
    public void TheStratifiedSpaceReachesEveryDimensionAndOutcomeClass()
    {
        var templates = new SortedDictionary<string, int>(StringComparer.Ordinal);
        var placements = new SortedDictionary<string, int>(StringComparer.Ordinal);
        var lineEndings = new SortedDictionary<string, int>(StringComparer.Ordinal);
        var executions = new SortedDictionary<string, int>(StringComparer.Ordinal);
        var groups = new SortedDictionary<string, int>(StringComparer.Ordinal);
        var surrogateClasses = new SortedDictionary<string, int>(StringComparer.Ordinal);
        var classSets = new SortedDictionary<string, int>(StringComparer.Ordinal);
        var parseOutcomes = new SortedDictionary<string, int>(StringComparer.Ordinal);
        var diagnosticKinds = new SortedDictionary<string, int>(StringComparer.Ordinal);
        var relations = new SortedDictionary<string, int>(StringComparer.Ordinal);
        var skips = new SortedDictionary<string, int>(StringComparer.Ordinal);
        var fingerprints = new HashSet<string>(StringComparer.Ordinal);

        var worstDiagnosticRatio = 0.0;
        var worstDiagnostics = 0;
        var worstAtOnePosition = 0;
        var worstSource = 0;
        var frontEndRuns = 0;

        foreach (var parameters in Space)
        {
            var report = Utf16Invariants.Run(Utf16Decoder.Encode(parameters));
            var testCase = report.Case;
            var observation = report.Observation;

            Count(templates, Utf16Tables.TemplateOf(parameters.Template).Id);
            Count(placements, parameters.Placement.ToString());
            Count(lineEndings, parameters.LineEndings.ToString());
            Count(executions, parameters.ExecutionMode.ToString());
            Count(groups, Utf16Fingerprint.InsertionId(parameters).Split('/')[0]);
            Count(surrogateClasses, testCase.SurrogateClass.ToString());
            Count(classSets, Utf16Fingerprint.ClassSetOf(testCase.CodeUnits));
            Count(parseOutcomes, observation.RawDiagnosticCount == 0 ? "clean" : "diagnostics");
            Count(diagnosticKinds, observation.FirstDiagnosticBucket);
            foreach (var relation in report.Relations.Checked) Count(relations, relation);
            foreach (var skip in report.Relations.Skipped) Count(skips, skip);
            fingerprints.Add(report.Fingerprint);

            if (observation.FrontEndRan) frontEndRuns++;
            worstSource = Math.Max(worstSource, observation.SourceLength);
            worstDiagnostics = Math.Max(worstDiagnostics, observation.RawDiagnosticCount);
            worstAtOnePosition = Math.Max(worstAtOnePosition, observation.MaxDiagnosticsAtOnePosition);
            worstDiagnosticRatio = Math.Max(
                worstDiagnosticRatio,
                observation.RawDiagnosticCount / (double)(observation.SourceLength + 1));
        }

        // Every dimension of the payload is genuinely reached.
        Assert.Equal(Utf16Tables.Templates.Length, templates.Count);
        Assert.Equal(Utf16Decoder.PlacementCount, placements.Count);
        Assert.Equal(Utf16Decoder.LineEndingCount, lineEndings.Count);
        Assert.Equal(Utf16Decoder.ExecutionCount, executions.Count);
        Assert.Equal(Enum.GetValues<Utf16SurrogateClass>().Length, surrogateClasses.Count);

        // Both outcome classes, and a real variety of diagnostics rather than one repeated kind.
        Assert.True(parseOutcomes.Count == 2, $"Only outcome classes: {string.Join(',', parseOutcomes.Keys)}");
        Assert.True(diagnosticKinds.Count >= 6, $"Only {diagnosticKinds.Count} distinct first-diagnostic kinds.");
        Assert.True(classSets.Count >= 20, $"Only {classSets.Count} distinct code-unit class sets.");
        Assert.True(frontEndRuns > Space.Length / 3, $"The frontend ran for only {frontEndRuns} of {Space.Length}.");

        // No single template may dominate the space; a lopsided walk hides whole templates.
        var largest = templates.Values.Max();
        Assert.True(
            largest < Space.Length / 2,
            $"One template covers {largest} of {Space.Length} points.");

        // The bounds the harness enforces are headroom over MEASURED worst cases, not guesses.
        Assert.True(
            worstDiagnosticRatio < Utf16Executor.DiagnosticsPerCodeUnit / 2.0,
            $"Worst diagnostics-per-code-unit was {worstDiagnosticRatio:F3}, too close to the " +
            $"{Utf16Executor.DiagnosticsPerCodeUnit} ceiling to be a meaningful bound.");
        Assert.True(
            worstAtOnePosition <= Utf16Executor.MaxDiagnosticsAtOnePosition,
            $"Worst diagnostics at one position was {worstAtOnePosition}, over the " +
            $"{Utf16Executor.MaxDiagnosticsAtOnePosition} ceiling.");

        WriteReport(
            templates, placements, lineEndings, executions, groups, surrogateClasses, classSets,
            parseOutcomes, diagnosticKinds, relations, skips, fingerprints.Count,
            worstSource, worstDiagnostics, worstAtOnePosition, worstDiagnosticRatio);
    }

    [Fact]
    public void EveryRelationIsFalsifiable_NotVacuouslyTrue()
    {
        // A relation nobody can break is not a test. Each one is shown here to REJECT a deliberately
        // wrong pair, using the same comparison the relation itself performs.
        var lf = "A = 1\nOutput = A";
        var crlf = "A = 1\r\nOutput = A";
        var loneCr = "A = 1\rOutput = A";

        // cr-transparency: identical tokens by line/column, and it would notice if they were not.
        var (lfTokens, _) = Lexer.Tokenize(lf);
        var (crlfTokens, _) = Lexer.Tokenize(crlf);
        var (crTokens, _) = Lexer.Tokenize(loneCr);
        Assert.Equal(
            lfTokens.Select(t => (t.Kind, t.Line, t.Column, t.Length)),
            crlfTokens.Select(t => (t.Kind, t.Line, t.Column, t.Length)));
        Assert.NotEqual(
            lfTokens.Select(t => (t.Kind, t.Line, t.Column, t.Length)),
            crTokens.Select(t => (t.Kind, t.Line, t.Column, t.Length)));

        // lone-cr-not-a-line-break: the whole lone-CR source really is one line, and the LF one is not.
        Assert.All(crTokens, t => Assert.Equal(1, t.Line));
        Assert.Contains(lfTokens, t => t.Line > 1);

        // trailing-newline-neutral: it compares real trees, and a CONTENT change does move them.
        var closed = Parser.ParseSyntax("Output = 'a'");
        var closedNewline = Parser.ParseSyntax("Output = 'a'\n");
        var different = Parser.ParseSyntax("Output = 'b'");
        Assert.Equal(
            FrontEndFingerprint.ComputeParseResult(closed.Root, closed.Diagnostics),
            FrontEndFingerprint.ComputeParseResult(closedNewline.Root, closedNewline.Diagnostics));
        Assert.NotEqual(
            FrontEndFingerprint.ComputeParseResult(closed.Root, closed.Diagnostics),
            FrontEndFingerprint.ComputeParseResult(different.Root, different.Diagnostics));

        // exact-string-preservation: it reads the real evaluated value, and it distinguishes
        // precomposed from decomposed text — which is exactly what a normalizing path would hide.
        Assert.Equal("\u00E9", StringValueOf("Output = '\u00E9'"));
        Assert.Equal("\u0065\u0301", StringValueOf("Output = '\u0065\u0301'"));
        Assert.NotEqual(StringValueOf("Output = '\u00E9'"), StringValueOf("Output = '\u0065\u0301'"));
    }

    [Fact]
    public void EveryInvariantTheHarnessClaimsIsProvenToFireOnABrokenInput()
    {
        var source = "A = 1\nOutput = A";
        var (tokens, _) = Lexer.Tokenize(source);

        // Token offset past the source.
        Expect(() => CheckOne(source, tokens.Select(t =>
            t.Kind == TokenKind.Identifier ? t with { Position = source.Length + 5 } : t)), "past the");

        // Token that consumes nothing — the forward-progress violation.
        Expect(() => CheckOne(source, tokens.Select(t =>
            t.Kind == TokenKind.Identifier ? t with { Length = 0 } : t)), "consumes no code units");

        // Two tokens at the same offset.
        Expect(() => CheckOne(source, tokens.Select(t =>
            t.Kind == TokenKind.Equals ? t with { Position = 0 } : t)), "strictly advance");

        // Recorded line/column disagreeing with the offset.
        Expect(() => CheckOne(source, tokens.Select(t =>
            t.Kind == TokenKind.Number ? t with { Line = 9 } : t)), "records (");

        // Token text that is not its source slice — a normalized or replaced code unit.
        Expect(() => CheckOne(source, tokens.Select(t =>
            t.Kind == TokenKind.Identifier ? t with { StringValue = "\uFFFD" } : t)), "not its source slice");

        // A token whose slice spans a line break, which would make its end column unsound.
        Expect(() => CheckOne(source, tokens.Select(t =>
            t.Kind == TokenKind.Number ? t with { Length = 3 } : t)), "spans a line break");

        // Missing end-of-file token.
        Expect(() => CheckOne(source, tokens.Where(t => t.Kind != TokenKind.EndOfFile)), "placement is wrong");
    }

    [Fact]
    public void TheDiagnosticBoundsAreReachableInPrincipleAndSoAreRealTests()
    {
        // A bound nothing can ever reach is decoration. These show the shapes that approach it.
        var manyBadCharacters = new string('\u0301', 200);           // 200 combining marks: 200 bad tokens
        var syntax = Parser.ParseSyntax(manyBadCharacters);
        Assert.True(syntax.Diagnostics.Count >= 200, $"Only {syntax.Diagnostics.Count} diagnostics.");
        Assert.True(
            syntax.Diagnostics.Count <= (Utf16Executor.DiagnosticsPerCodeUnit * (manyBadCharacters.Length + 1))
                                        + Utf16Executor.DiagnosticsConstant,
            "A source of pure bad characters already exceeds the structural ceiling.");

        // Every one of those diagnostics is at its OWN position: reporting tracks consumption.
        var positions = syntax.Diagnostics
            .Where(d => d.Span is not null)
            .Select(d => (d.Span!.StartLineNumber, d.Span.StartColumn))
            .ToHashSet();
        Assert.Equal(syntax.Diagnostics.Count, positions.Count);
    }

    [Fact]
    public void DiagnosticsAtOnePositionAreBoundedByTheParsersOwnNestingGuard()
    {
        // Unclosed nested delimiters are the shape that stacks diagnostics at ONE position: every
        // open level reports "expected the closer" at end of file. Input is fully consumed the whole
        // time, so this is NOT a stalled recovery loop — it is one diagnostic per open construct, and
        // open constructs are capped by Parser.MaxNestingDepth. That cap, not a hand-picked number,
        // is the bound the harness enforces.
        var worst = 0;
        var worstShape = "";

        foreach (var opener in new[] { '[', '(', '{' })
        foreach (var count in new[] { 1, 2, 8, 64, 288, 600, 2048 })
        {
            var source = new string(opener, count);
            var syntax = Parser.ParseSyntax(source);

            var atOnePosition = syntax.Diagnostics
                .Where(d => d.Span is not null)
                .GroupBy(d => (d.Span!.StartLineNumber, d.Span.StartColumn))
                .Select(g => g.Count())
                .DefaultIfEmpty(0)
                .Max();

            if (atOnePosition > worst)
            {
                worst = atOnePosition;
                worstShape = $"{count}x'{opener}'";
            }

            // Whatever the recovery does, every code unit is still consumed exactly once.
            var (tokens, _) = Lexer.Tokenize(source);
            Assert.Equal(count + 1, tokens.Count);
            Assert.Equal(source.Length, tokens[^1].Position);
        }

        // The bound is REACHED in a meaningful sense — a shape gets well past the old guess of 16,
        // which is exactly why that guess was wrong — and is never exceeded.
        Assert.True(worst > 16, $"Worst diagnostics at one position was only {worst} ({worstShape}).");
        Assert.True(
            worst <= Utf16Executor.MaxDiagnosticsAtOnePosition,
            $"{worst} diagnostics shared one position for {worstShape}, over the " +
            $"{Utf16Executor.MaxDiagnosticsAtOnePosition} the harness allows.");
        Assert.Equal(Parser.MaxNestingDepth, Utf16Executor.MaxDiagnosticsAtOnePosition);
    }

    [Fact]
    public void FrontEndEligibilityIsReal_AndTheFrontEndSeesTheSameDiagnostics()
    {
        var ran = 0;
        foreach (var parameters in Space.Where(p => p.ExecutionMode != Utf16ExecutionMode.ParseSyntax).Take(300))
        {
            var built = Utf16SourceBuilder.Build(parameters);
            var syntax = Parser.ParseSyntax(built.Source);
            var frontEnd = FrontEndPipeline.Process(built.Source);

            // The frontend may ADD diagnostics; it may never drop or rewrite a parser one.
            Assert.True(frontEnd.Diagnostics.Count >= syntax.Diagnostics.Count);
            for (var i = 0; i < syntax.Diagnostics.Count; i++)
            {
                Assert.Equal(syntax.Diagnostics[i].Severity, frontEnd.Diagnostics[i].Severity);
                Assert.Equal(syntax.Diagnostics[i].Message, frontEnd.Diagnostics[i].Message);
                Assert.Equal(syntax.Diagnostics[i].Span, frontEnd.Diagnostics[i].Span);
            }

            // Every frontend span is still in range for THIS source, not a previous one.
            var widths = SourceSpanValidator.LineWidths(built.Source);
            foreach (var diagnostic in frontEnd.Diagnostics)
                Assert.Null(SourceSpanValidator.Validate(diagnostic.Span, widths));

            ran++;
        }

        Assert.True(ran >= 200, $"Only {ran} frontend-eligible cases were checked.");
    }

    [Fact]
    public void ReplayFidelityHolds_ForEveryStratifiedPayload()
    {
        // Replay's promise: the payload alone reconstructs the exact code units. Verified over the
        // whole space, through the canonical payload the corpus and seeds actually carry.
        foreach (var parameters in Space)
        {
            var payload = Utf16Decoder.Encode(parameters);
            var direct = Utf16SourceBuilder.Build(parameters);
            var replayed = Utf16SourceBuilder.Build(Utf16Decoder.Decode(payload));
            Assert.Equal(direct.HexUnits, replayed.HexUnits);
        }
    }

    // ── Helpers ──────────────────────────────────────────────────────────────

    private static string StringValueOf(string source)
    {
        var run = KatLangEngine.Run(source);
        var success = Assert.IsType<RunResult.Success>(run);
        return Assert.IsType<Result.Str>(success.Value).Value;
    }

    /// <summary>Runs the token invariants over a doctored stream via the real checker.</summary>
    private static void CheckOne(string source, IEnumerable<Token> tokens)
        => Utf16Executor.CheckTokens(source, [.. tokens]);

    private static void Expect(Action action, string expectedFragment)
    {
        var exception = Assert.Throws<Utf16InvariantException>(action);
        Assert.Contains(expectedFragment, exception.Message, StringComparison.Ordinal);
    }

    private static void Count(SortedDictionary<string, int> counts, string key)
        => counts[key] = counts.GetValueOrDefault(key) + 1;

    private static void WriteReport(
        SortedDictionary<string, int> templates,
        SortedDictionary<string, int> placements,
        SortedDictionary<string, int> lineEndings,
        SortedDictionary<string, int> executions,
        SortedDictionary<string, int> groups,
        SortedDictionary<string, int> surrogateClasses,
        SortedDictionary<string, int> classSets,
        SortedDictionary<string, int> parseOutcomes,
        SortedDictionary<string, int> diagnosticKinds,
        SortedDictionary<string, int> relations,
        SortedDictionary<string, int> skips,
        int distinctFingerprints,
        int worstSource,
        int worstDiagnostics,
        int worstAtOnePosition,
        double worstRatio)
    {
        var path = Environment.GetEnvironmentVariable("KATLANG_UTF16_READINESS_REPORT");
        if (string.IsNullOrWhiteSpace(path)) return;

        var report = new StringBuilder(8192);
        report.AppendLine(CultureInfo.InvariantCulture, $"stratified points: {Space.Length}");
        report.AppendLine(CultureInfo.InvariantCulture, $"distinct fingerprints: {distinctFingerprints}");
        report.AppendLine(CultureInfo.InvariantCulture, $"worst source code units: {worstSource}");
        report.AppendLine(CultureInfo.InvariantCulture, $"worst diagnostics: {worstDiagnostics}");
        report.AppendLine(CultureInfo.InvariantCulture, $"worst diagnostics at one position: {worstAtOnePosition}");
        report.AppendLine(CultureInfo.InvariantCulture, $"worst diagnostics per code unit: {worstRatio:F3}");
        Section(report, "template", templates);
        Section(report, "placement", placements);
        Section(report, "line ending", lineEndings);
        Section(report, "execution", executions);
        Section(report, "group", groups);
        Section(report, "surrogate class", surrogateClasses);
        Section(report, "code-unit class set", classSets);
        Section(report, "parse outcome", parseOutcomes);
        Section(report, "first diagnostic", diagnosticKinds);
        Section(report, "relation checked", relations);
        Section(report, "relation skipped", skips);

        Directory.CreateDirectory(Path.GetDirectoryName(Path.GetFullPath(path))!);
        File.WriteAllText(path, report.ToString());
        _ = RepoRoot.Find();
    }

    private static void Section(StringBuilder report, string title, SortedDictionary<string, int> counts)
    {
        report.AppendLine().AppendLine(CultureInfo.InvariantCulture, $"{title} ({counts.Count}):");
        foreach (var (key, value) in counts)
            report.AppendLine(CultureInfo.InvariantCulture, $"    {key} = {value}");
    }
}
