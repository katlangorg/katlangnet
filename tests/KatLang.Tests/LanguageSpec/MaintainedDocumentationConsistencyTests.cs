using System.Text.RegularExpressions;

namespace KatLang.Tests.LanguageSpec;

/// <summary>
/// Keeps the maintained descriptions of KatLang telling one story on the rules the
/// September 2026 pre-release documentation sweep found drifting apart. Behavior is pinned
/// by the executable specification; these checks guard only prose that RESTATES it:
/// <list type="bullet">
///   <item>the operator-precedence ladder, restated in five places, keeps the frozen tier
///   order (<c>or</c> &lt; <c>xor</c> &lt; <c>and</c> &lt; prefix <c>not</c> &lt; the ONE
///   comparison tier &lt; <c>+ -</c> &lt; <c>* / div mod</c> &lt; prefix <c>-</c> &lt;
///   <c>^</c>);</item>
///   <item>the user-facing guides state that indexing is zero-based;</item>
///   <item>no current-rule text uses a formulation that is the SHAPE of a superseded rule:
///   a number glossed as a truth value, <c>not</c> placed against two comparison tiers, or
///   <c>exported</c> — an EXPOSURE classification — used where only the PUBLIC visibility of
///   an <c>open</c> member or the DECLARED members of structural navigation are meant
///   (K1-08: selection never depends on exposure).</item>
/// </list>
/// Historical records (the alignment manifest, the dated design notes) narrate superseded
/// rules on purpose and are not scanned; tests are not scanned either, because they quote
/// stale shapes to reject them.
/// </summary>
public class MaintainedDocumentationConsistencyTests
{
    /// <summary>Documents that state the CURRENT language rules.</summary>
    private static readonly string[] CurrentRuleDocuments =
    [
        "AGENTS.md",
        "README.md",
        "tutorial.md",
        "KatLang.ebnf",
        ".github/agents/katlang-generator.agent.md",
        "experimental/prompts/katlang-generator.txt",
        "docs/design/language-rules/README.md",
        "docs/design/language-rules/syntax.md",
        "docs/design/language-rules/sequences-lists-and-calls.md",
        "docs/design/language-rules/ownership-and-lookup.md",
        "docs/design/language-rules/evaluator-and-hosting.md",
        "docs/design/language-rules/editor-semantics.md",
        "src/KatLang/CALLABLES.md",
        "src/KatLang/BINDING-ARCHITECTURE.md",
    ];

    /// <summary>
    /// Formulations that express a superseded rule. Each is narrow on purpose: it matches the
    /// shape the stale rule took, never a topic, so current prose about the same subject is
    /// unaffected.
    /// </summary>
    public static TheoryData<string, string> StaleShapes() => new()
    {
        // Booleans are a value kind with no numeric encoding: `x == y` is `true`, never `1` (true).
        { @"(?<![\w.])`?[01]`?\s*\((?:true|false)\)", "a number glossed as a Boolean truth value" },
        // Equality and ordering share ONE comparison tier; `not` binds below all six.
        { @"(?:comparison and equality|equality and comparison) operators", "two comparison tiers" },
        // Structural dot navigation selects DECLARED members and then checks accessibility.
        { @"exported structural members?", "exposure-filtered structural navigation" },
        // `open` selects PUBLIC members; exposure is checked on the selected member afterwards.
        { @"\bpublic\s*(?:\+|and)?\s*exported\b", "open selection by exposure" },
        { @"\bexported\s+(?:propert(?:y|ies)|members?)\s+for\b", "public visibility called 'exported'" },
        { @"\bexport(?:ed|s)?\s+(?:\w+\s+){0,3}(?:through|via|by)\s+`?open\b", "public visibility called 'exported'" },
        { @"\bproviders?\s+exports?\b", "public visibility called 'exported'" },
        { @"\bexported\s+(?:clause-style\s+)?APIs?\b", "public visibility called 'exported'" },
        // Indexing is zero-based (source line/column coordinates are 1-based, a different thing).
        { @"\b(?:one|1)-based\s+(?:index|indexing|selection)\b", "one-based indexing" },
    };

    [Theory]
    [MemberData(nameof(StaleShapes))]
    public void CurrentRuleText_NeverUsesTheShapeOfASupersededRule(string pattern, string supersededRule)
    {
        var regex = new Regex(pattern, RegexOptions.IgnoreCase | RegexOptions.CultureInvariant);
        var hits = new List<string>();
        var scanned = 0;
        foreach (var (relativePath, text) in CurrentRuleTexts())
        {
            scanned++;
            var lines = text.ReplaceLineEndings("\n").Split('\n');
            for (var index = 0; index < lines.Length; index++)
            {
                if (regex.Match(lines[index]) is { Success: true } match)
                    hits.Add($"{relativePath}:{index + 1}: '{match.Value}'");
            }
        }

        // The source and Lean scan is not allowed to silently shrink to nothing.
        Assert.True(scanned > CurrentRuleDocuments.Length + 100, $"Only {scanned} files were scanned.");
        Assert.True(
            hits.Count == 0,
            $"Current-rule text uses the shape of a superseded rule ({supersededRule}):\n" + string.Join("\n", hits));
    }

    /// <summary>
    /// Every restatement of the operator-precedence ladder lists the tiers in the frozen
    /// order and names every tier. Tokens are compared by TIER, so a tier's internal spelling
    /// order and the presentation (a one-line ladder, a numbered list, the tutorial's
    /// reference table read bottom-up) are free.
    /// </summary>
    [Theory]
    [InlineData("AGENTS.md")]
    [InlineData("docs/design/language-rules/syntax.md")]
    [InlineData(".github/agents/katlang-generator.agent.md")]
    [InlineData("experimental/prompts/katlang-generator.txt")]
    [InlineData("tutorial.md")]
    public void PrecedenceLadder_ListsTheFrozenTiersInOrder(string relativePath)
    {
        var text = File.ReadAllText(Path.Combine(RepoRoot.Find(), relativePath)).ReplaceLineEndings("\n");
        var tokens = relativePath switch
        {
            "experimental/prompts/katlang-generator.txt" => NumberedLadderTokens(text),
            "tutorial.md" => ReferenceTableLadderTokens(text),
            _ => InlineLadderTokens(text),
        };

        var tier = 0;
        var tiersSeen = new HashSet<int>();
        foreach (var token in tokens)
        {
            // The smallest tier at or above the current one that spells the token: `-` is
            // additive right after `+` and prefix minus after the multiplicative tier.
            var next = -1;
            for (var candidate = tier; candidate < PrecedenceTiers.Length && next < 0; candidate++)
            {
                if (PrecedenceTiers[candidate].Contains(token))
                    next = candidate;
            }

            Assert.True(next >= 0, $"{relativePath}: `{token}` appears out of precedence order in the ladder [{string.Join(" ", tokens)}].");
            tier = next;
            tiersSeen.Add(tier);
        }

        Assert.True(
            tiersSeen.Count == PrecedenceTiers.Length,
            $"{relativePath}: the ladder [{string.Join(" ", tokens)}] does not name every precedence tier.");
    }

    /// <summary>
    /// The user-facing guides state the index base explicitly: selection counts from zero.
    /// </summary>
    [Theory]
    [InlineData("tutorial.md")]
    [InlineData(".github/agents/katlang-generator.agent.md")]
    [InlineData("experimental/prompts/katlang-generator.txt")]
    public void UserFacingGuide_StatesZeroBasedIndexing(string relativePath)
    {
        var text = File.ReadAllText(Path.Combine(RepoRoot.Find(), relativePath));
        Assert.Contains("zero-based", text, StringComparison.OrdinalIgnoreCase);
    }

    /// <summary>Loosest first. Prefix <c>-</c> is its own tier, above the multiplicative one.</summary>
    private static readonly string[][] PrecedenceTiers =
    [
        ["or"],
        ["xor"],
        ["and"],
        ["not"],
        ["<", ">", "<=", ">=", "==", "!="],
        ["+", "-"],
        ["*", "/", "div", "mod"],
        ["-"],
        ["^"],
    ];

    private static readonly HashSet<string> LadderOperators =
        [.. PrecedenceTiers.SelectMany(static tier => tier)];

    private static readonly Regex BacktickedToken = new("`([^`]+)`", RegexOptions.CultureInvariant);

    /// <summary>A one-line ladder <c>`or` &lt; `xor` &lt; … &lt; `^`</c>: from its first rung through `^`.</summary>
    private static List<string> InlineLadderTokens(string text)
    {
        var start = text.IndexOf("`or` < `xor`", StringComparison.Ordinal);
        Assert.True(start >= 0, "No one-line precedence ladder starting with `or` < `xor` was found.");
        var end = text.IndexOf("`^`", start, StringComparison.Ordinal);
        Assert.True(end > start, "The one-line precedence ladder does not reach `^`.");
        return OperatorTokens(text[start..(end + "`^`".Length)]);
    }

    /// <summary>The numbered list under "Operator precedence, lowest to highest:".</summary>
    private static List<string> NumberedLadderTokens(string text)
    {
        var header = text.IndexOf("Operator precedence, lowest to highest:\n", StringComparison.Ordinal);
        Assert.True(header >= 0, "No numbered precedence ladder was found.");
        var rungs = text[header..]
            .Split('\n')
            .Skip(1)
            .TakeWhile(static line => Regex.IsMatch(line, @"^\d+\. "));
        return OperatorTokens(string.Join("\n", rungs));
    }

    /// <summary>The reference table's operator rows from the Highest row to the Lowest row, read bottom-up.</summary>
    private static List<string> ReferenceTableLadderTokens(string text)
    {
        var header = text.IndexOf("| Operator | Description | Precedence |", StringComparison.Ordinal);
        Assert.True(header >= 0, "No operator reference table was found.");
        var rows = new List<string>();
        foreach (var line in text[header..].Split('\n').Skip(2))
        {
            Assert.StartsWith("|", line);
            rows.Add(line.Split('|')[1]);
            if (line.TrimEnd().EndsWith("| Lowest |", StringComparison.Ordinal))
                break;
        }

        rows.Reverse();
        return OperatorTokens(string.Join("\n", rows));
    }

    private static List<string> OperatorTokens(string ladder)
        => BacktickedToken.Matches(ladder)
            .Select(static match => match.Groups[1].Value)
            .Where(LadderOperators.Contains)
            .ToList();

    private static IEnumerable<(string RelativePath, string Text)> CurrentRuleTexts()
    {
        var root = RepoRoot.Find();
        foreach (var relativePath in CurrentRuleDocuments)
            yield return (relativePath, File.ReadAllText(Path.Combine(root, relativePath)));

        // Source comments and Lean doc comments state the same laws. Build output and
        // package caches (bin, obj, .lake) are not source.
        foreach (var (directory, pattern) in new[] { ("src/KatLang", "*.cs"), ("lean", "*.lean") })
        {
            foreach (var path in Directory.EnumerateFiles(Path.Combine(root, directory), pattern, SearchOption.AllDirectories))
            {
                var relativePath = Path.GetRelativePath(root, path).Replace('\\', '/');
                if (relativePath.Split('/').Any(static segment => segment is "bin" or "obj" || segment.StartsWith('.')))
                    continue;

                yield return (relativePath, File.ReadAllText(path));
            }
        }
    }
}
