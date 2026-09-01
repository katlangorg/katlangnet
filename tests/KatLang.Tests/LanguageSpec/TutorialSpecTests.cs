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

    private static IReadOnlyList<string> CommentTexts(string source) =>
        Lexer.Tokenize(source).Tokens
            .Where(token => token.Kind == TokenKind.Comment)
            .Select(token => token.StringValue ?? string.Empty)
            .ToArray();

    /// <summary>
    /// Marker-linked projection of the shared tutorial parse
    /// (<see cref="TutorialCorpus"/>, which also enforces the structural
    /// grammar: marker adjacency, fence termination, recognized claim forms).
    /// </summary>
    private static IReadOnlyList<LinkedExample> ParseLinkedExamples() =>
        TutorialCorpus.Examples
            .Where(e => e.SpecCaseId is not null)
            .Select(e => new LinkedExample(
                e.SpecCaseId!,
                e.MarkerLine!.Value,
                e.Source,
                e.ClaimKind == TutorialClaimKind.InlineValue ? e.InlineValue : null,
                e.ClaimKind == TutorialClaimKind.Error,
                e.ClaimKind == TutorialClaimKind.FencedRows ? e.ResultsFence : null))
            .ToArray();

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
                var tutorialDisplay = TutorialCorpus.StripPresentationBlanks(fence);
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
