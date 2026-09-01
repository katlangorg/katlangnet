namespace KatLang.Tests.LanguageSpec;

/// <summary>
/// Synthetic-markdown tests for the shared tutorial parser. The sweep's
/// accounting is only as strong as this grammar: a malformed future tutorial
/// must fail with an actionable message, never silently drop a result claim
/// out of verification.
/// </summary>
public class TutorialCorpusParserTests
{
    private static TutorialExample Single(string markdown)
        => Assert.Single(TutorialCorpus.Parse(markdown));

    [Fact]
    public void OrdinaryFenceWithInlineResult_IsRecognized()
    {
        var example = Single("## Section\n\n```\n1 + 2\n```\n\n**Result:** `3`\n");

        Assert.Equal(3, example.FenceLine);
        Assert.Equal("Section", example.Section);
        Assert.Equal("1 + 2", example.Source);
        Assert.Equal(TutorialClaimKind.InlineValue, example.ClaimKind);
        Assert.Equal("3", example.ClaimedDisplay);
        Assert.True(example.HasResultClaim);
    }

    [Fact]
    public void SingularAndPluralInlineLabels_AreBothRecognized()
    {
        Assert.Equal("7", Single("```\n7\n```\n**Results:** `7`\n").ClaimedDisplay);
        Assert.Equal("7", Single("```\n7\n```\n**Result:** `7`\n").ClaimedDisplay);
    }

    [Fact]
    public void InlineResultSupportsAMatchingLongerBacktickDelimiter()
    {
        var example = Single("```\n'a`b'\n```\n**Result:** ``a`b``\n");
        Assert.Equal("a`b", example.ClaimedDisplay);
    }

    [Theory]
    [InlineData("**Result:** ``a`b`")]
    [InlineData("**Result:** `a`b``")]
    public void MismatchedInlineBacktickDelimiterFailsLoudly(string label)
    {
        var failure = Assert.Throws<InvalidOperationException>(() =>
            TutorialCorpus.Parse($"```\n'a`b'\n```\n{label}\n"));
        Assert.Contains("unrecognized result label", failure.Message);
    }

    [Fact]
    public void FenceWithoutClaim_HasNoResultClaim()
    {
        var example = Single("```\nvalue = 6 # style demo\n```\n\nProse after.\n");

        Assert.Equal(TutorialClaimKind.None, example.ClaimKind);
        Assert.False(example.HasResultClaim);
        Assert.Null(example.ClaimedDisplay);
    }

    [Fact]
    public void FencedResultsBlock_CapturesRowsAndStripsPresentationBlanks()
    {
        var example = Single("```\n1, 2\n3\n```\n\n**Results:**\n```\n1\n2\n\n3\n```\n");

        Assert.Equal(TutorialClaimKind.FencedRows, example.ClaimKind);
        Assert.Equal("1\n2\n\n3", example.ResultsFence);
        Assert.Equal("1\n2\n3", example.ClaimedDisplay);
    }

    [Fact]
    public void ErrorClaim_IsRecognized()
    {
        var example = Single("```\nA = {\n}\nA\n```\n\n**Result:** error — `A` has no defined output.\n");

        Assert.Equal(TutorialClaimKind.Error, example.ClaimKind);
        Assert.Contains("no defined output", example.ErrorClaimText);
        Assert.Null(example.ClaimedDisplay);
    }

    [Fact]
    public void SkipMarker_AttachesReasonToResultBearingFence()
    {
        var example = Single("<!-- spec:skip needs a network downloader -->\n```\nopen 'https://x'\nX\n```\n**Result:** `1`\n");

        Assert.Equal("needs a network downloader", example.SkipReason);
        Assert.Null(example.SpecCaseId);
        Assert.Equal(1, example.MarkerLine);
        Assert.True(example.HasResultClaim);
    }

    [Fact]
    public void SpecMarker_AttachesCaseId()
    {
        var example = Single("<!-- spec:first-program -->\n```\n2 + 3 * 4\n```\n\n**Result:** `14`\n");

        Assert.Equal("first-program", example.SpecCaseId);
        Assert.Null(example.SkipReason);
        Assert.Equal(1, example.MarkerLine);
    }

    [Fact]
    public void EquivalentWhitespaceBeforeSpecMarkerNameIsRecognized()
    {
        var example = Single("<!--spec:first-program-->\n```\n2 + 3 * 4\n```\n**Result:** `14`\n");
        Assert.Equal("first-program", example.SpecCaseId);
        Assert.Equal(1, example.MarkerLine);
    }

    [Fact]
    public void MisCasedSpecMarkerFailsInsteadOfBecomingProse()
    {
        var failure = Assert.Throws<InvalidOperationException>(() =>
            TutorialCorpus.Parse("<!-- Spec:skip reason -->\n```\n1\n```\n**Result:** `1`\n"));
        Assert.Contains("malformed spec marker", failure.Message);
    }

    [Theory]
    [InlineData("<!-- spec:skip -->\n```\n1\n```\n**Result:** `1`\n")]
    [InlineData("<!-- spec:skip    -->\n```\n1\n```\n**Result:** `1`\n")]
    public void BlankSkipReason_Fails(string markdown)
    {
        var failure = Assert.Throws<InvalidOperationException>(() => TutorialCorpus.Parse(markdown));
        Assert.Contains("non-blank reason", failure.Message);
    }

    [Fact]
    public void SkipOnClaimlessFence_Fails()
    {
        var failure = Assert.Throws<InvalidOperationException>(() =>
            TutorialCorpus.Parse("<!-- spec:skip whatever reason -->\n```\n1\n```\n\nProse.\n"));
        Assert.Contains("no result claim", failure.Message);
    }

    [Fact]
    public void NeighboringFences_StayIndependentExamples()
    {
        var examples = TutorialCorpus.Parse("```\nX*\nY\n```\n\nis interpreted as:\n\n```\nX*, Y\n```\n");

        Assert.Equal(2, examples.Count);
        Assert.All(examples, e => Assert.False(e.HasResultClaim));
        Assert.Equal(["X*\nY", "X*, Y"], examples.Select(e => e.Source));
    }

    [Fact]
    public void ProseMentioningResultMidSentence_IsIgnored()
    {
        var examples = TutorialCorpus.Parse(
            "Examples labelled **Result** produce one output.\n\n```\n1\n```\n\nThe result window shows rows.\n");

        Assert.False(Assert.Single(examples).HasResultClaim);
    }

    [Fact]
    public void ResultLabelNotAttachedToAFence_Fails()
    {
        var failure = Assert.Throws<InvalidOperationException>(() =>
            TutorialCorpus.Parse("Some prose.\n\n**Result:** `3`\n"));
        Assert.Contains("not attached to a source fence", failure.Message);
    }

    [Fact]
    public void SecondResultLabelAfterConsumedClaim_Fails()
    {
        var failure = Assert.Throws<InvalidOperationException>(() =>
            TutorialCorpus.Parse("```\n1\n```\n**Result:** `1`\n**Result:** `2`\n"));
        Assert.Contains("not attached to a source fence", failure.Message);
    }

    [Fact]
    public void UnrecognizedResultLabelForm_FailsInsteadOfSilentlyDroppingTheClaim()
    {
        var failure = Assert.Throws<InvalidOperationException>(() =>
            TutorialCorpus.Parse("```\n1 + 2\n```\n\n**Result:** 3\n"));
        Assert.Contains("unrecognized result label", failure.Message);
    }

    [Theory]
    [InlineData(" **Result:** `3`")]
    [InlineData("Result: `3`")]
    [InlineData("**Result**: `3`")]
    [InlineData("**result:** `3`")]
    [InlineData("** Result : ** `3`")]
    [InlineData("> **Result:** `3`")]
    [InlineData("- **Result:** `3`")]
    [InlineData("### Result: `3`")]
    public void ResultLabelNearMisses_FailLoudly(string label)
    {
        var failure = Assert.Throws<InvalidOperationException>(() =>
            TutorialCorpus.Parse($"```\n1 + 2\n```\n\n{label}\n"));
        Assert.Contains("unrecognized result label", failure.Message);
    }

    [Fact]
    public void ErrorPrefixMustEndAtAWordBoundary()
    {
        var failure = Assert.Throws<InvalidOperationException>(() =>
            TutorialCorpus.Parse("```\n1\n```\n**Result:** errorless prose\n"));
        Assert.Contains("unrecognized result label", failure.Message);
    }

    [Theory]
    [InlineData("Explanatory prose.\n")]
    [InlineData("## Intervening heading\n")]
    public void InterveningContentCannotReassociateAResultClaim(string intervening)
    {
        var failure = Assert.Throws<InvalidOperationException>(() =>
            TutorialCorpus.Parse($"```\n1\n```\n\n{intervening}\n**Result:** `1`\n"));
        Assert.Contains("not attached to a source fence", failure.Message);
    }

    [Fact]
    public void ConsecutiveFencesAttachAClaimOnlyToTheNearestFence()
    {
        var examples = TutorialCorpus.Parse(
            "```\n1\n```\n\n```\n2\n```\n\n**Result:** `2`\n");

        Assert.Equal(2, examples.Count);
        Assert.False(examples[0].HasResultClaim);
        Assert.Equal("1", examples[0].Source);
        Assert.Equal(TutorialClaimKind.InlineValue, examples[1].ClaimKind);
        Assert.Equal("2", examples[1].Source);
        Assert.Equal("2", examples[1].ClaimedDisplay);
    }

    [Fact]
    public void WhitespaceOnlyBlankLinesStillAllowDirectAttachment()
    {
        var example = Single("```\n1 + 2\n```\n \t \n**Result:** `3`\n");
        Assert.Equal(TutorialClaimKind.InlineValue, example.ClaimKind);
        Assert.Equal("3", example.ClaimedDisplay);
    }

    [Theory]
    [InlineData("  ```\n  1\n  ```\n\n  **Result:** `1`\n")]
    [InlineData("> ```\n> 1\n> ```\n\n> **Result:** `1`\n")]
    [InlineData("````\n1\n````\n\n**Result:** `1`\n")]
    [InlineData("```katlang\n1\n```\n\n**Result:** `1`\n")]
    [InlineData("``` \n1\n```\n\n**Result:** `1`\n")]
    public void UnsupportedRelevantFenceForms_FailLoudly(string markdown)
    {
        _ = Assert.Throws<InvalidOperationException>(() => TutorialCorpus.Parse(markdown));
    }

    [Fact]
    public void FourBacktickExampleContainingTripleBackticks_FailsLoudly()
    {
        const string markdown = "````markdown\n```\n1\n```\n**Result:** `1`\n````\n";
        _ = Assert.Throws<InvalidOperationException>(() => TutorialCorpus.Parse(markdown));
    }

    [Fact]
    public void EmptyFencedDisplayIsStillAResultBearingClaim()
    {
        var example = Single("```\n()*\n```\n**Result:**\n```\n```\n");
        Assert.Equal(TutorialClaimKind.FencedRows, example.ClaimKind);
        Assert.Equal(string.Empty, example.ClaimedDisplay);
        Assert.True(example.HasResultClaim);
    }

    [Fact]
    public void TaggedFence_IsNotAKatLangExample()
    {
        Assert.Empty(TutorialCorpus.Parse("```text\nnot katlang\n```\n\nProse.\n"));
    }

    [Fact]
    public void TaggedFenceFollowedByResultClaim_FailsAsDetachedClaim()
    {
        var failure = Assert.Throws<InvalidOperationException>(() =>
            TutorialCorpus.Parse("```text\noutput\n```\n\n**Result:** `3`\n"));
        Assert.Contains("not attached to a source fence", failure.Message);
    }

    [Fact]
    public void CrlfAndLfInputs_ParseIdentically()
    {
        const string lf = "## S\n\n```\n1 + 2\n```\n\n**Result:** `3`\n";
        var crlf = lf.Replace("\n", "\r\n");

        Assert.Equal(TutorialCorpus.Parse(lf), TutorialCorpus.Parse(crlf));
    }

    [Fact]
    public void UnterminatedFence_Fails()
    {
        var failure = Assert.Throws<InvalidOperationException>(() => TutorialCorpus.Parse("```\n1 + 2\n"));
        Assert.Contains("unterminated fence", failure.Message);
    }

    [Fact]
    public void BareResultsLabelWithoutOutputFence_Fails()
    {
        var failure = Assert.Throws<InvalidOperationException>(() =>
            TutorialCorpus.Parse("```\n1\n```\n\n**Results:**\n\nProse instead of a fence.\n"));
        Assert.Contains("fenced output block", failure.Message);
    }

    [Theory]
    [InlineData("<!-- spec:some-case -->\nProse before the fence.\n```\n1\n```\n")]
    [InlineData("<!-- spec:some-case -->\n## Heading\n```\n1\n```\n")]
    [InlineData("<!-- spec:some-case -->\n")]
    public void MarkerNotFollowedByABareFence_Fails(string markdown)
    {
        var failure = Assert.Throws<InvalidOperationException>(() => TutorialCorpus.Parse(markdown));
        Assert.Contains("immediately followed by a bare ``` fence", failure.Message);
    }

    [Fact]
    public void MarkerFollowedByTaggedFence_Fails()
    {
        var failure = Assert.Throws<InvalidOperationException>(() =>
            TutorialCorpus.Parse("<!-- spec:some-case -->\n```text\n1\n```\n"));
        Assert.Contains("immediately followed by a bare ``` fence", failure.Message);
    }

    [Fact]
    public void TwoMarkersOnOneFence_Fail()
    {
        var failure = Assert.Throws<InvalidOperationException>(() =>
            TutorialCorpus.Parse("<!-- spec:case-a -->\n<!-- spec:skip some reason -->\n```\n1\n```\n**Result:** `1`\n"));
        Assert.Contains("one fence takes exactly one marker", failure.Message);
    }

    [Theory]
    [InlineData("<!-- spec: -->\n")]
    [InlineData("<!-- spec:two words -->\n")]
    [InlineData("<!-- spec:missing-terminator\n")]
    public void MalformedMarker_Fails(string markdown)
    {
        var failure = Assert.Throws<InvalidOperationException>(() => TutorialCorpus.Parse(markdown));
        Assert.Contains("malformed spec marker", failure.Message);
    }

    [Fact]
    public void SectionTracking_UsesNearestHeadingOutsideFences()
    {
        var examples = TutorialCorpus.Parse(
            "## First\n\n```\n1\n```\n\n### Nested: `avg`\n\n```\n# not a heading — a KatLang comment\n2\n```\n");

        Assert.Equal(["First", "Nested: `avg`"], examples.Select(e => e.Section));
    }

    [Fact]
    public void RealTutorial_ParsesAndSweepPartitionsAreCoherent()
    {
        var examples = TutorialCorpus.Examples;

        // Structural sanity over the real corpus: ordinals are dense, claimed
        // examples expose a comparable display or error text, and skip reasons
        // are never blank (the parser rejects blank reasons at parse time).
        Assert.Equal(Enumerable.Range(0, examples.Count), examples.Select(e => e.Index));
        Assert.All(examples.Where(e => e.ClaimKind is TutorialClaimKind.InlineValue or TutorialClaimKind.FencedRows),
            e => Assert.NotNull(e.ClaimedDisplay));
        Assert.All(examples.Where(e => e.ClaimKind == TutorialClaimKind.Error),
            e => Assert.NotNull(e.ErrorClaimText));
        Assert.All(examples.Where(e => e.SkipReason is not null),
            e => Assert.False(string.IsNullOrWhiteSpace(e.SkipReason)));
    }

    [Fact]
    public void ParsedCollectionsAreReadOnlyIncludingTheCachedCorpus()
    {
        var parsed = TutorialCorpus.Parse("```\n1\n```\n**Result:** `1`\n");
        var mutableView = Assert.IsAssignableFrom<IList<TutorialExample>>(parsed);
        Assert.True(mutableView.IsReadOnly);
        Assert.Throws<NotSupportedException>(() => mutableView.Clear());

        var cachedView = Assert.IsAssignableFrom<IList<TutorialExample>>(TutorialCorpus.Examples);
        Assert.True(cachedView.IsReadOnly);
        Assert.Throws<NotSupportedException>(() => cachedView.Clear());
    }
}
