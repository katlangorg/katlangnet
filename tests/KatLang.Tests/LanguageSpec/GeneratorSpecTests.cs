using System.Text;

namespace KatLang.Tests.LanguageSpec;

/// <summary>
/// Keeps the katlang-generator prompt files in sync with the canonical
/// specification: a marker-delimited verified-examples block is generated
/// deterministically from the corpus cases flagged
/// <see cref="SpecCase.IncludeInGeneratorPrompt"/> and embedded in BOTH prompt
/// files, so the two prompts can no longer drift apart on those examples and
/// every embedded expectation is engine- and Lean-verified through the
/// corpus. A failure means the block is stale — regenerate with:
///   $env:KATLANG_REGENERATE_LANGUAGE_SPEC = "1"
///   dotnet test .\KatLang.slnx --filter LanguageSpecArtifacts
/// (This class shares the LanguageSpecArtifacts regeneration filter.)
/// </summary>
public class LanguageSpecArtifactsGeneratorPromptTests
{
    private const string BeginMarker = "=== BEGIN GENERATED: katlang-spec-examples (DO NOT EDIT BY HAND) ===";
    private const string EndMarker = "=== END GENERATED: katlang-spec-examples ===";

    private static readonly string[] PromptFiles =
    [
        ".github/agents/katlang-generator.agent.md",
        "experimental/prompts/katlang-generator.txt",
    ];

    public static TheoryData<string> PromptFilePaths()
    {
        var data = new TheoryData<string>();
        foreach (var file in PromptFiles)
            data.Add(file);
        return data;
    }

    [Theory]
    [MemberData(nameof(PromptFilePaths))]
    public void PromptFile_ContainsFreshGeneratedExamplesBlock(string relativePath)
    {
        var path = Path.Combine(RepoRoot.Find(), relativePath);
        Assert.True(File.Exists(path), $"{relativePath} not found.");

        var expectedBlock = RenderBlock();
        var raw = File.ReadAllText(path);
        var content = raw.ReplaceLineEndings("\n");

        if (Environment.GetEnvironmentVariable(LanguageSpecArtifactsTests.RegenerateVariable) == "1")
        {
            var updated = ReplaceOrAppendBlock(content, expectedBlock);
            // Preserve the file's existing line-ending convention.
            if (raw.Contains("\r\n", StringComparison.Ordinal))
                updated = updated.Replace("\n", "\r\n", StringComparison.Ordinal);
            File.WriteAllText(path, updated);
            return;
        }

        var begin = content.IndexOf(BeginMarker, StringComparison.Ordinal);
        var end = content.IndexOf(EndMarker, StringComparison.Ordinal);
        Assert.True(begin >= 0 && end > begin,
            $"{relativePath} is missing the generated katlang-spec-examples block. " +
            $"Set {LanguageSpecArtifactsTests.RegenerateVariable}=1 and rerun this test to insert it.");

        var actualBlock = content[begin..(end + EndMarker.Length)];
        Assert.True(expectedBlock == actualBlock,
            $"{relativePath}: the generated katlang-spec-examples block is out of date with the canonical corpus. " +
            $"Set {LanguageSpecArtifactsTests.RegenerateVariable}=1, rerun this test, and review the diff.");
    }

    [Theory]
    [MemberData(nameof(PromptFilePaths))]
    public void PromptFile_UsesOnlyCanonicalCollectingAndSpreadGuidance(string relativePath)
    {
        var content = File.ReadAllText(Path.Combine(RepoRoot.Find(), relativePath));

        // Collecting bindings: postfix `name...` is the one canonical spelling.
        Assert.Contains(
            "Postfix `name...` is the ONLY collecting-binding syntax",
            content,
            StringComparison.Ordinal);

        // Spreading: the named intrinsic, in both spellings, producing a SUPPLY.
        Assert.Contains("spread(items)", content, StringComparison.Ordinal);
        Assert.Contains("items.spread", content, StringComparison.Ordinal);
        Assert.Contains(
            "produces an item supply and does not return a list or sequence",
            content,
            StringComparison.Ordinal);

        // The canonical forwarding example must be present.
        Assert.Contains(
            "Forward(items...) = Target(spread(items))",
            content,
            StringComparison.Ordinal);
    }

    private static string ReplaceOrAppendBlock(string content, string block)
    {
        var begin = content.IndexOf(BeginMarker, StringComparison.Ordinal);
        var end = content.IndexOf(EndMarker, StringComparison.Ordinal);
        if (begin >= 0 && end > begin)
            return content[..begin] + block + content[(end + EndMarker.Length)..];

        var trimmed = content.TrimEnd('\n');
        return trimmed + "\n\n" + block + "\n";
    }

    internal static string RenderBlock()
    {
        var cases = LanguageSpecCorpus.AllCases();
        var selected = cases.Where(c => c.IncludeInGeneratorPrompt).ToList();

        var builder = new StringBuilder();
        builder.Append(BeginMarker);
        builder.Append('\n');
        builder.Append($"""

            Verified reference examples ({selected.Count} of the {cases.Count}-case canonical language specification,
            tests/KatLang.Tests/LanguageSpec/LanguageSpecCorpus.cs). Every program and expected
            output below is executed against the KatLang engine and (where representable)
            guarded against the Lean model on every build. Treat these as ground truth for the
            language behaviors they demonstrate.

            Regenerate this block from the repo root with:
              $env:KATLANG_REGENERATE_LANGUAGE_SPEC = "1"
              dotnet test .\KatLang.slnx --filter LanguageSpecArtifacts

            """.ReplaceLineEndings("\n"));

        foreach (var specCase in selected)
        {
            builder.Append('\n');
            builder.Append($"[{specCase.Id}] {specCase.Explanation}\n\n");
            foreach (var line in specCase.Source.Split('\n'))
                builder.Append(line.Length == 0 ? "\n" : $"    {line}\n");

            switch (specCase.Outcome)
            {
                case SpecOutcome.Evaluates:
                    builder.Append("\n  Displays:\n");
                    foreach (var row in specCase.ExpectedDisplay!.Split('\n'))
                        builder.Append($"    {row}\n");
                    break;
                case SpecOutcome.EvalError:
                    builder.Append($"\n  Fails with an evaluation error ({specCase.ExpectedErrorCategory}).\n");
                    break;
                case SpecOutcome.ParseError:
                    builder.Append("\n  Rejected by the parser");
                    builder.Append(specCase.ExpectedParseDiagnosticFragment is { } fragment
                        ? $": \"{fragment} ...\"\n"
                        : ".\n");
                    break;
            }
        }

        builder.Append('\n');
        builder.Append(EndMarker);
        return builder.ToString();
    }
}
