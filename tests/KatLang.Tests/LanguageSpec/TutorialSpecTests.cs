using System.Text.RegularExpressions;

namespace KatLang.Tests.LanguageSpec;

/// <summary>
/// Verifies that tutorial examples linked to canonical specification cases
/// via <c>&lt;!-- spec:case-id --&gt;</c> markers stay in sync: the fenced
/// source must match the canonical case source exactly, and the displayed
/// expected output must match the canonical (engine-verified) display. A
/// failure means the tutorial silently changed a linked example, a case was
/// renamed without updating the tutorial, or a canonical expectation changed
/// without a tutorial update.
/// </summary>
public class TutorialSpecTests
{
    private sealed record LinkedExample(
        string CaseId,
        int MarkerLine,          // 1-based
        string FenceSource,
        string? InlineResult,    // **Result:** `X`
        bool InlineErrorResult,  // **Result:** error — ...
        string? ResultsFence);   // **Results:**/**Result:** + fenced block (verbatim, may contain blank lines)

    private static readonly Regex MarkerPattern = new(@"^<!--\s*spec:(?<id>\S+)\s*-->\s*$");

    private static string TutorialPath => Path.Combine(RepoRoot.Find(), "tutorial.md");

    private static IReadOnlyList<string> CommentTexts(string source) =>
        Lexer.Tokenize(source).Tokens
            .Where(token => token.Kind == TokenKind.Comment)
            .Select(token => token.StringValue ?? string.Empty)
            .ToArray();

    private static IReadOnlyList<LinkedExample> ParseLinkedExamples()
    {
        var lines = File.ReadAllText(TutorialPath).ReplaceLineEndings("\n").Split('\n');
        var examples = new List<LinkedExample>();

        for (var i = 0; i < lines.Length; i++)
        {
            var marker = MarkerPattern.Match(lines[i]);
            if (!marker.Success)
            {
                Assert.False(lines[i].Contains("<!-- spec", StringComparison.Ordinal),
                    $"tutorial.md line {i + 1}: malformed spec marker '{lines[i].Trim()}'.");
                continue;
            }

            var caseId = marker.Groups["id"].Value;
            var cursor = i + 1;
            while (cursor < lines.Length && lines[cursor].Length == 0)
                cursor++;

            Assert.True(cursor < lines.Length && lines[cursor] == "```",
                $"tutorial.md line {i + 1}: marker spec:{caseId} must be immediately followed by a bare ``` fence.");

            var fenceStart = ++cursor;
            while (cursor < lines.Length && lines[cursor] != "```")
                cursor++;
            Assert.True(cursor < lines.Length, $"tutorial.md: unterminated fence after spec:{caseId}.");
            var fenceSource = string.Join("\n", lines[fenceStart..cursor]);
            cursor++; // past closing fence

            while (cursor < lines.Length && lines[cursor].Length == 0)
                cursor++;

            string? inlineResult = null;
            var inlineError = false;
            string? resultsFence = null;
            if (cursor < lines.Length)
            {
                var inline = Regex.Match(lines[cursor], @"^\*\*Results?:\*\* `(?<value>.+)`\s*$");
                if (inline.Success)
                {
                    inlineResult = inline.Groups["value"].Value;
                }
                else if (Regex.IsMatch(lines[cursor], @"^\*\*Results?:\*\* error"))
                {
                    inlineError = true;
                }
                else if (Regex.IsMatch(lines[cursor], @"^\*\*Results?:\*\*\s*$"))
                {
                    cursor++;
                    while (cursor < lines.Length && lines[cursor].Length == 0)
                        cursor++;
                    Assert.True(cursor < lines.Length && lines[cursor] == "```",
                        $"tutorial.md: spec:{caseId} has a Results heading without a fenced output block.");
                    var resultsStart = ++cursor;
                    while (cursor < lines.Length && lines[cursor] != "```")
                        cursor++;
                    Assert.True(cursor < lines.Length, $"tutorial.md: unterminated results fence for spec:{caseId}.");
                    resultsFence = string.Join("\n", lines[resultsStart..cursor]);
                }
            }

            examples.Add(new LinkedExample(caseId, i + 1, fenceSource, inlineResult, inlineError, resultsFence));
        }

        return examples;
    }

    [Fact]
    public void LinkedExamples_ReferenceExistingCasesExactlyOnce()
    {
        var cases = LanguageSpecCorpus.AllCases().ToDictionary(c => c.Id);
        var seen = new HashSet<string>(StringComparer.Ordinal);
        var examples = ParseLinkedExamples();

        Assert.True(examples.Count >= 15,
            $"Expected at least 15 tutorial-linked spec cases, found {examples.Count}; markers may have been mass-removed.");

        foreach (var example in examples)
        {
            Assert.True(cases.ContainsKey(example.CaseId),
                $"tutorial.md line {example.MarkerLine}: spec:{example.CaseId} does not exist in LanguageSpecCorpus (missing or renamed case id).");
            Assert.True(seen.Add(example.CaseId),
                $"tutorial.md line {example.MarkerLine}: spec:{example.CaseId} is referenced more than once.");
        }
    }

    [Fact]
    public void LinkedExamples_SourceMatchesCanonicalCase()
    {
        var cases = LanguageSpecCorpus.AllCases().ToDictionary(c => c.Id);
        foreach (var example in ParseLinkedExamples())
        {
            if (!cases.TryGetValue(example.CaseId, out var specCase))
                continue; // reported by LinkedExamples_ReferenceExistingCasesExactlyOnce

            Assert.True(specCase.Source == example.FenceSource,
                $"tutorial.md line {example.MarkerLine}: fenced source for spec:{example.CaseId} differs from the canonical case source.\n" +
                $"--- canonical ---\n{specCase.Source}\n--- tutorial ---\n{example.FenceSource}");
        }
    }

    [Fact]
    public void LinkedExamples_ExpectedOutputMatchesCanonicalDisplay()
    {
        var cases = LanguageSpecCorpus.AllCases().ToDictionary(c => c.Id);
        foreach (var example in ParseLinkedExamples())
        {
            if (!cases.TryGetValue(example.CaseId, out var specCase))
                continue;

            if (example.InlineErrorResult)
            {
                Assert.True(specCase.Outcome == SpecOutcome.EvalError,
                    $"tutorial.md line {example.MarkerLine}: spec:{example.CaseId} shows an error result but the canonical case outcome is {specCase.Outcome}.");
                continue;
            }

            if (example.InlineResult is { } inline)
            {
                Assert.True(specCase.Outcome == SpecOutcome.Evaluates,
                    $"tutorial.md line {example.MarkerLine}: spec:{example.CaseId} shows a value result but the canonical case outcome is {specCase.Outcome}.");
                Assert.True(specCase.ExpectedDisplay == inline,
                    $"tutorial.md line {example.MarkerLine}: spec:{example.CaseId} inline result `{inline}` differs from canonical display `{specCase.ExpectedDisplay}`.");
                continue;
            }

            if (example.ResultsFence is { } fence)
            {
                // Blank lines inside a Results fence are presentation-only
                // grouping (one group per source row); the display rows are
                // the non-blank lines in order.
                var tutorialRows = fence.Split('\n').Where(l => l.Length > 0);
                var tutorialDisplay = string.Join("\n", tutorialRows);
                Assert.True(specCase.ExpectedDisplay == tutorialDisplay,
                    $"tutorial.md line {example.MarkerLine}: spec:{example.CaseId} results block differs from canonical display.\n" +
                    $"--- canonical ---\n{specCase.ExpectedDisplay}\n--- tutorial (blank-stripped) ---\n{tutorialDisplay}");
                continue;
            }

            // No adjacent Result(s) convention: the fence must carry its
            // claims as inline comments (verified by the comment-claims lint
            // below); require at least one comment so a marker is never
            // silently unverified.
            Assert.True(CommentTexts(example.FenceSource).Count > 0,
                $"tutorial.md line {example.MarkerLine}: spec:{example.CaseId} has neither a Result(s) block nor inline `#` claims.");
        }
    }

    /// <summary>
    /// Comment-claims lint: when every value-literal trailing comment in a
    /// linked fence lines up one-to-one with the canonical display rows, the
    /// claims must match the rows. (Prose comments are ignored; fences whose
    /// claim count differs from the row count are skipped — they are covered
    /// by the source-match check plus the canonical case's own runner
    /// verification.)
    /// </summary>
    [Fact]
    public void LinkedExamples_InlineValueClaimsMatchDisplayRows()
    {
        var cases = LanguageSpecCorpus.AllCases().ToDictionary(c => c.Id);

        foreach (var example in ParseLinkedExamples())
        {
            if (!cases.TryGetValue(example.CaseId, out var specCase)
                || specCase.Outcome != SpecOutcome.Evaluates)
            {
                continue;
            }

            var claims = CommentTexts(example.FenceSource)
                .Select(comment => comment.Trim())
                .Where(IsValueLiteral)
                .ToList();

            var rows = specCase.ExpectedDisplay!.Split('\n');
            if (claims.Count != rows.Length)
                continue;

            for (var i = 0; i < rows.Length; i++)
            {
                Assert.True(claims[i] == rows[i],
                    $"tutorial.md line {example.MarkerLine}: spec:{example.CaseId} row {i} comment claims `{claims[i]}` but the canonical display row is `{rows[i]}`.");
            }
        }
    }

    [Fact]
    public void InlineClaimExtraction_IgnoresHashesInsideStrings()
    {
        Assert.Empty(CommentTexts("'# is string content'"));
        Assert.Equal([" 7"], CommentTexts("'# is string content' # 7"));
    }

    private static bool IsValueLiteral(string claim) =>
        claim == "()"
        || claim == "[]"
        || Regex.IsMatch(claim, @"^-?[0-9]+(\.[0-9]+)?$")
        || (claim.StartsWith('(') && claim.EndsWith(')') && Regex.IsMatch(claim, @"^[0-9,()\[\]'\-. ]+$"))
        || (claim.StartsWith('[') && claim.EndsWith(']') && Regex.IsMatch(claim, @"^[0-9,()\[\]'\-. ]+$"));
}
