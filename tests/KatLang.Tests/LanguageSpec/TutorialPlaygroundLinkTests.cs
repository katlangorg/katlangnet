namespace KatLang.Tests.LanguageSpec;

/// <summary>
/// Every tutorial example is followed by an <c>[Open in Playground](https://katlang.org/#1/…)</c>
/// line: the code link of the example's exact source, which opens and runs it in the playground,
/// as the examples of katlang.org's About page do. Changing an example changes its link, so this
/// test fails until the links are regenerated: set <c>KATLANG_REGENERATE_TUTORIAL_PLAYGROUND_LINKS=1</c>
/// for one run of this class, which rewrites the link lines of tutorial.md and then fails by design.
/// </summary>
public class TutorialPlaygroundLinkTests
{
    [Fact]
    public void EveryExample_IsFollowedByThePlaygroundLinkOfItsExactSource()
    {
        const string relativePath = "tutorial.md";
        var markdown = File.ReadAllText(Path.Combine(RepoRoot.Find(), relativePath));

        ArtifactRegeneration.VerifyOrRegenerate(
            RegenerationFlags.TutorialPlaygroundLinks,
            relativePath,
            regenerate: () => TutorialCorpus.WithPlaygroundLinks(markdown),
            verify: () =>
            {
                var examples = TutorialCorpus.Examples;
                Assert.NotEmpty(examples);
                foreach (var example in examples)
                {
                    var expected = TutorialCorpus.PlaygroundLinkLineFor(example.Source);
                    Assert.True(
                        example.PlaygroundLink is not null,
                        $"{example.Identity} has no playground link after it; the next line should be:\n{expected}");
                    Assert.True(
                        TutorialCorpus.PlaygroundLinkLabel + example.PlaygroundLink + ")" == expected,
                        $"The playground link after {example.Identity} does not open its source; it should be:\n{expected}");
                    Assert.True(
                        CodeLink.DecodeLink(example.PlaygroundLink) is CodeLinkDecoding.Program { Source: var linked }
                            && linked == example.Source,
                        $"The playground link after {example.Identity} does not decode to its source.");
                }

                // A link line belongs to the example above it: none stands anywhere else.
                var linkLines = markdown.ReplaceLineEndings("\n").Split('\n')
                    .Count(line => line.StartsWith(TutorialCorpus.PlaygroundLinkLabel, StringComparison.Ordinal));
                Assert.Equal(examples.Count, linkLines);
            });
    }

    [Fact]
    public void LinkDetection_FindsTheLinkThatFollowsAnExample_AfterItsClaim()
    {
        var link = TutorialCorpus.PlaygroundLinkLineFor("1");
        var examples = TutorialCorpus.Parse($"```\n1\n```\n\n**Result:** `1`\n\n{link}\n\n```\n2\n```\n\nProse.\n");

        Assert.Equal(2, examples.Count);
        Assert.Equal(5, examples[0].EndLine);
        Assert.Equal(7, examples[0].PlaygroundLinkLine);
        Assert.Equal(link, TutorialCorpus.PlaygroundLinkLabel + examples[0].PlaygroundLink + ")");
        Assert.Equal(11, examples[1].EndLine);
        Assert.Null(examples[1].PlaygroundLink);
        Assert.Null(examples[1].PlaygroundLinkLine);
    }

    [Fact]
    public void Regeneration_AddsMissingLinks_ReplacesStaleOnes_AndIsIdempotent()
    {
        var stale = TutorialCorpus.PlaygroundLinkLineFor("99");
        var markdown = $"## A\n\n```\n1\n```\n\n**Results:**\n```\n1\n```\n\n{stale}\n\n```\n2\n```\n\nProse.\n";

        var regenerated = TutorialCorpus.WithPlaygroundLinks(markdown);

        var expected =
            $"## A\n\n```\n1\n```\n\n**Results:**\n```\n1\n```\n\n{TutorialCorpus.PlaygroundLinkLineFor("1")}\n\n"
            + $"```\n2\n```\n\n{TutorialCorpus.PlaygroundLinkLineFor("2")}\n\nProse.\n";
        Assert.Equal(expected, regenerated);
        Assert.Equal(regenerated, TutorialCorpus.WithPlaygroundLinks(regenerated));
    }
}
