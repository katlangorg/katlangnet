using System.Text.RegularExpressions;

namespace KatLang.Tests.LeanProofModules;

/// <summary>
/// The shared contract of the GENERATED Lean proof modules whose generator lives in this folder: a module under
/// <c>lean/KatLangArityLaws/</c> whose text is produced from templates over an instance table, or from another
/// module's proof text under a renaming, instead of being written by hand.
///
/// <para>Each module has one generator test here, one registered <see cref="RegenerationFlags"/> entry, and a
/// header that names both. The generator is the ONLY writer: the module is never edited by hand, and a
/// verification run compares and never writes (see <see cref="ArtifactRegeneration"/>).</para>
///
/// <para><b>What is and is not checked here.</b> These tests pin the module's TEXT to its generator. They prove
/// nothing: whether the generated proofs hold is decided by <c>lake build KatLangArityLaws</c>, which a
/// regeneration must be followed by.</para>
///
/// <para>The generators are deterministic and self-contained: fixed tables in fixed order, no clock, no
/// environment, no tool outside the .NET SDK. They need no Python.</para>
/// </summary>
internal static class LeanProofModuleArtifact
{
    /// <summary>The Lean target that compiles every module generated in this folder.</summary>
    public const string LeanTarget = "KatLangArityLaws";

    /// <summary>
    /// Compares the tracked module at <paramref name="artifactRelativePath"/> (repo-relative) with
    /// <paramref name="generated"/>, or — when <paramref name="flag"/> requests it — writes the generated text
    /// there and fails by design.
    /// </summary>
    public static void VerifyOrRegenerate(RegenerationFlag flag, string artifactRelativePath, string generated)
    {
        var path = Path.Combine(RepoRoot.Find(), artifactRelativePath);

        ArtifactRegeneration.VerifyOrRegenerate(
            flag,
            artifactRelativePath,
            regenerate: () => generated,
            verify: () => Verify(flag, artifactRelativePath, path, generated),
            afterRegenerating: $"run `lake build {LeanTarget}` to check the proofs");
    }

    /// <summary>
    /// The observational half, with the path factored out so it can be tested against a scratch file: the
    /// module at <paramref name="path"/> must exist and hold exactly <paramref name="generated"/> (line endings
    /// aside — a CRLF checkout is the same text). It reads and never writes.
    /// </summary>
    internal static void Verify(RegenerationFlag flag, string displayPath, string path, string generated)
    {
        Assert.True(File.Exists(path),
            $"{displayPath} is missing. Set {flag}=1 and rerun this test to generate it (that run fails by design).");

        var tracked = File.ReadAllText(path).ReplaceLineEndings("\n");
        Assert.True(generated == tracked,
            $"{displayPath} differs from its generator's output. The module is GENERATED text and is never edited by " +
            $"hand: change the generator, set {flag}=1 and rerun this test to regenerate the module (that run fails by " +
            $"design), review the diff, and run `lake build {LeanTarget}` to check the proofs. " +
            DescribeFirstDifference(generated, tracked));
    }

    private static readonly Regex Placeholder = new("@([A-Z]+)@", RegexOptions.CultureInvariant);

    /// <summary>
    /// Fills the <c>@NAME@</c> placeholders of <paramref name="template"/> in ONE pass, so a value is never
    /// scanned for placeholders. A placeholder with no value and a value with no placeholder are both refused:
    /// a template and its table cannot drift apart silently.
    /// </summary>
    public static string Fill(string template, params (string Name, string Value)[] values)
    {
        var byName = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var (name, value) in values)
        {
            if (!byName.TryAdd(name, value))
                throw new InvalidOperationException($"The placeholder @{name}@ is given two values.");
        }

        var used = new HashSet<string>(StringComparer.Ordinal);
        var filled = Placeholder.Replace(template, match =>
        {
            var name = match.Groups[1].Value;
            if (!byName.TryGetValue(name, out var value))
                throw new InvalidOperationException($"The template has the placeholder @{name}@, which is given no value.");

            used.Add(name);
            return value;
        });

        var unused = byName.Keys.Where(name => !used.Contains(name)).OrderBy(name => name, StringComparer.Ordinal).ToList();
        if (unused.Count > 0)
            throw new InvalidOperationException($"The template has no placeholder for: {string.Join(", ", unused.Select(name => $"@{name}@"))}.");

        return filled;
    }

    /// <summary>
    /// Replaces every occurrence of <paramref name="old"/> and refuses any count other than
    /// <paramref name="expectedCount"/>: a rewrite of copied proof text that silently stops applying, or starts
    /// applying somewhere new, would otherwise produce a module that differs from the reviewed one in an
    /// unreviewed place.
    /// </summary>
    public static string ReplaceExactly(string text, string old, string replacement, int expectedCount)
    {
        var found = CountOccurrences(text, old);
        if (found != expectedCount)
        {
            throw new InvalidOperationException(
                $"Expected {expectedCount} occurrence(s) of the text below, found {found}.{Environment.NewLine}{old}");
        }

        return text.Replace(old, replacement, StringComparison.Ordinal);
    }

    /// <summary>Non-overlapping occurrences, left to right (the occurrences <see cref="string.Replace(string, string)"/> replaces).</summary>
    public static int CountOccurrences(string text, string value)
    {
        ArgumentException.ThrowIfNullOrEmpty(value);

        var count = 0;
        for (var index = text.IndexOf(value, StringComparison.Ordinal); index >= 0; index = text.IndexOf(value, index + value.Length, StringComparison.Ordinal))
            count++;

        return count;
    }

    /// <summary>
    /// The first line the two texts differ in, with a window around the first differing column (a generated
    /// proof line can be thousands of characters long).
    /// </summary>
    internal static string DescribeFirstDifference(string generated, string tracked)
    {
        var generatedLines = generated.Split('\n');
        var trackedLines = tracked.Split('\n');
        var shared = Math.Min(generatedLines.Length, trackedLines.Length);
        var line = 0;
        while (line < shared && generatedLines[line] == trackedLines[line])
            line++;

        if (line == generatedLines.Length && line == trackedLines.Length)
            return "The texts are equal.";

        var generatedLine = line < generatedLines.Length ? generatedLines[line] : null;
        var trackedLine = line < trackedLines.Length ? trackedLines[line] : null;
        var column = 0;
        if (generatedLine is not null && trackedLine is not null)
        {
            var sharedColumns = Math.Min(generatedLine.Length, trackedLine.Length);
            while (column < sharedColumns && generatedLine[column] == trackedLine[column])
                column++;
        }

        return $"First difference at line {line + 1}, column {column + 1} " +
            $"(generated: {generatedLines.Length} lines, tracked: {trackedLines.Length} lines).{Environment.NewLine}" +
            $"Generated: {Window(generatedLine, column)}{Environment.NewLine}" +
            $"Tracked:   {Window(trackedLine, column)}";
    }

    private static string Window(string? line, int column)
    {
        if (line is null)
            return "<end of file>";

        const int Before = 60;
        const int After = 100;
        var start = Math.Max(0, column - Before);
        var end = Math.Min(line.Length, column + After);
        return (start > 0 ? "…" : "") + line[start..end] + (end < line.Length ? "…" : "");
    }
}
