using System.Text.RegularExpressions;

namespace KatLang.Tests.LanguageSpec;

/// <summary>Kind of result claim attached to a tutorial source fence.</summary>
public enum TutorialClaimKind
{
    /// <summary>No adjacent <c>**Result(s):**</c> label — the fence claims no executable output.</summary>
    None,

    /// <summary><c>**Result:** `value`</c> — one inline display row.</summary>
    InlineValue,

    /// <summary><c>**Results:**</c> (or <c>**Result:**</c>) followed by a fenced output block.</summary>
    FencedRows,

    /// <summary><c>**Result:** error — ...</c> — the example intentionally fails to evaluate.</summary>
    Error,
}

/// <summary>
/// One column-0 source fence of tutorial.md with its attached result claim and
/// markers. Output fences (the fenced block following a bare
/// <c>**Results:**</c> label) are consumed into <see cref="ResultsFence"/> and
/// never appear as examples themselves.
/// </summary>
public sealed record TutorialExample(
    int Index,               // ordinal among source fences, 0-based
    int FenceLine,           // 1-based line of the opening ```
    string Section,          // nearest heading text above the fence (hashes stripped)
    string Source,           // fence body, "\n"-joined
    TutorialClaimKind ClaimKind,
    string? InlineValue,     // InlineValue claims: the backticked value
    string? ResultsFence,    // FencedRows claims: verbatim block (may contain presentation blank rows)
    string? ErrorClaimText,  // Error claims: the full label line
    int? MarkerLine,         // 1-based line of the spec/skip marker, when present
    string? SpecCaseId,      // <!-- spec:case-id --> linkage
    string? SkipReason)      // <!-- spec:skip reason --> escape hatch
{
    /// <summary>True when the fence documents an executable outcome (value or error).</summary>
    public bool HasResultClaim => ClaimKind != TutorialClaimKind.None;

    /// <summary>
    /// The claimed display rows ("\n"-joined) for value claims; null for
    /// error/no-claim fences. Blank rows inside a Results fence are
    /// presentation-only grouping and are stripped, exactly as the
    /// marker-linked comparison has always done.
    /// </summary>
    public string? ClaimedDisplay => ClaimKind switch
    {
        TutorialClaimKind.InlineValue => InlineValue,
        TutorialClaimKind.FencedRows => TutorialCorpus.StripPresentationBlanks(ResultsFence!),
        _ => null,
    };

    /// <summary>Human identity for failure messages and skip inventories.</summary>
    public string Identity =>
        $"tutorial.md fence at line {FenceLine} [{Section}] first row `{FirstSourceRow}`";

    /// <summary>First non-blank source row — a line-number-independent fingerprint.</summary>
    public string FirstSourceRow =>
        Source.Split('\n').FirstOrDefault(l => l.Length > 0) ?? string.Empty;
}

/// <summary>
/// The one parser for tutorial.md's executable-example conventions, shared by
/// the marker-linkage tests (<see cref="TutorialSpecTests"/>) and the
/// result-claim sweep (<see cref="TutorialResultSweepTests"/>) so the two can
/// never disagree about what a fence, claim, or marker is.
///
/// <para>Grammar (all failures throw with the offending line number):</para>
/// <list type="bullet">
/// <item>A column-0 <c>```</c> line opens a fence; the body runs to the next
/// column-0 <c>```</c> line (which must be exactly <c>```</c>). Indented
/// fences are prose-level illustrations and are ignored. A TAGGED column-0
/// fence (<c>```text</c>) is consumed but is not a KatLang example.</item>
/// <item>The first non-blank line (whitespace-only rows count as blank) after a bare source fence may be a result
/// claim: <c>**Result:** `value`</c> (inline), <c>**Result:** error ...</c>
/// (error), or a bare <c>**Results:**</c>/<c>**Result:**</c> label followed by
/// a bare fenced output block. Label-like near misses (including plain,
/// differently emphasized/cased, indented, list, blockquote, and heading
/// forms) fail parsing, so formatting drift cannot silently drop a claim out
/// of the sweep.</item>
/// <item><c>&lt;!-- spec:case-id --&gt;</c> links the following fence to a
/// canonical case; <c>&lt;!-- spec:skip reason --&gt;</c> excludes the
/// following result-bearing fence from execution with a mandatory non-blank
/// reason. A marker must be immediately followed (blank lines allowed) by a
/// bare fence; a skip requires the fence to carry a result claim.</item>
/// </list>
/// </summary>
public static class TutorialCorpus
{
    private static readonly Regex MarkerShell = new(@"^<!--\s*spec:(?<body>.*?)\s*-->\s*$");
    private static readonly Regex SpecMarkerCandidate = new(@"<!--\s*spec", RegexOptions.IgnoreCase);
    private static readonly Regex CaseIdPattern = new(@"^\S+$");
    private static readonly Regex InlineResultPattern = new(
        @"^\*\*Results?:\*\* (?<ticks>(?>`+))(?<value>.*?)(?<!`)\k<ticks>(?!`)\s*$");
    private static readonly Regex ErrorResultPattern = new(@"^\*\*Results?:\*\* error(?:\s.*)?$");
    private static readonly Regex BareResultsLabelPattern = new(@"^\*\*Results?:\*\*\s*$");
    private static readonly Regex ResultLabelCandidatePattern = new(
        @"^\s*(?:(?:>\s*)|(?:[-+*]\s+)|(?:\d+[.)]\s+))*(?:#{1,6}\s+)?"
        + @"\*{0,2}\s*Results?\s*\*{0,2}\s*:",
        RegexOptions.IgnoreCase);
    private static readonly Regex HeadingPattern = new(@"^(?<hashes>#{1,6})\s+(?<text>.*)$");

    private static readonly Lazy<IReadOnlyList<TutorialExample>> Cached = new(() =>
        Parse(File.ReadAllText(Path.Combine(RepoRoot.Find(), "tutorial.md"))));

    /// <summary>All source fences of the repository tutorial, parsed once per test run.</summary>
    public static IReadOnlyList<TutorialExample> Examples => Cached.Value;

    /// <summary>Blank rows inside a Results fence are presentation-only grouping.</summary>
    public static string StripPresentationBlanks(string resultsFence) =>
        string.Join("\n", resultsFence.Split('\n').Where(l => l.Length > 0));

    public static IReadOnlyList<TutorialExample> Parse(string markdown)
    {
        var lines = markdown.ReplaceLineEndings("\n").Split('\n');
        var examples = new List<TutorialExample>();
        var section = "(preamble)";
        int? markerLine = null;
        string? specCaseId = null;
        string? skipReason = null;
        var i = 0;

        void RequireNoPendingMarker(string what, int atLine)
        {
            if (markerLine is { } pending)
            {
                throw new InvalidOperationException(
                    $"tutorial.md line {pending}: a spec marker must be immediately followed by a bare ``` fence, "
                    + $"but line {atLine} is {what}.");
            }
        }

        while (i < lines.Length)
        {
            var line = lines[i];

            if (line.StartsWith("```", StringComparison.Ordinal))
            {
                var fenceLine = i + 1;
                if (line != "```")
                {
                    // Tagged fence: not a KatLang example. A pending marker or a
                    // following Result label would be dangling and fails below.
                    RequireNoPendingMarker($"a tagged fence ({line})", fenceLine);
                    i = ConsumeFenceBody(lines, i, fenceLine, out _);
                    continue;
                }

                i = ConsumeFenceBody(lines, i, fenceLine, out var source);

                var claimKind = TutorialClaimKind.None;
                string? inlineValue = null;
                string? resultsFence = null;
                string? errorClaimText = null;

                var k = SkipBlanks(lines, i);
                if (k < lines.Length && LooksLikeResultLabel(lines[k]))
                {
                    var claimLine = lines[k];
                    var inline = InlineResultPattern.Match(claimLine);
                    if (inline.Success)
                    {
                        claimKind = TutorialClaimKind.InlineValue;
                        inlineValue = inline.Groups["value"].Value;
                        i = k + 1;
                    }
                    else if (ErrorResultPattern.IsMatch(claimLine))
                    {
                        claimKind = TutorialClaimKind.Error;
                        errorClaimText = claimLine;
                        i = k + 1;
                    }
                    else if (BareResultsLabelPattern.IsMatch(claimLine))
                    {
                        var fenceStart = SkipBlanks(lines, k + 1);
                        if (fenceStart >= lines.Length || lines[fenceStart] != "```")
                        {
                            throw new InvalidOperationException(
                                $"tutorial.md line {k + 1}: a bare Result(s) label must be followed by a bare "
                                + "``` fenced output block.");
                        }

                        i = ConsumeFenceBody(lines, fenceStart, fenceStart + 1, out resultsFence);
                        claimKind = TutorialClaimKind.FencedRows;
                    }
                    else
                    {
                        throw new InvalidOperationException(
                            $"tutorial.md line {k + 1}: unrecognized result label '{claimLine.Trim()}'. "
                            + "Supported claim forms: `**Result:** `value``, `**Result:** error ...`, or a bare "
                            + "`**Results:**` label followed by a fenced output block.");
                    }
                }

                if (skipReason is not null && claimKind == TutorialClaimKind.None)
                {
                    throw new InvalidOperationException(
                        $"tutorial.md line {markerLine}: spec:skip marks a fence with no result claim; "
                        + "only result-bearing examples need (or may carry) a skip reason.");
                }

                examples.Add(new TutorialExample(
                    examples.Count, fenceLine, section, source, claimKind,
                    inlineValue, resultsFence, errorClaimText, markerLine, specCaseId, skipReason));
                markerLine = null;
                specCaseId = null;
                skipReason = null;
                continue;
            }

            if (SpecMarkerCandidate.IsMatch(line))
            {
                var shell = MarkerShell.Match(line);
                if (!shell.Success)
                {
                    throw new InvalidOperationException(
                        $"tutorial.md line {i + 1}: malformed spec marker '{line.Trim()}'.");
                }

                if (markerLine is { } previous)
                {
                    throw new InvalidOperationException(
                        $"tutorial.md line {i + 1}: a second spec marker before the fence at which the marker "
                        + $"on line {previous} points; one fence takes exactly one marker.");
                }

                var body = shell.Groups["body"].Value;
                if (body == "skip" || body.StartsWith("skip ", StringComparison.Ordinal)
                    || body.StartsWith("skip\t", StringComparison.Ordinal))
                {
                    var reason = body.Length > 4 ? body[4..].Trim() : string.Empty;
                    if (reason.Length == 0)
                    {
                        throw new InvalidOperationException(
                            $"tutorial.md line {i + 1}: spec:skip requires a non-blank reason "
                            + "(<!-- spec:skip why this example cannot run standalone -->).");
                    }

                    skipReason = reason;
                }
                else if (CaseIdPattern.IsMatch(body))
                {
                    specCaseId = body;
                }
                else
                {
                    throw new InvalidOperationException(
                        $"tutorial.md line {i + 1}: malformed spec marker '{line.Trim()}' — the marker body "
                        + "must be a single case id or `skip <reason>`.");
                }

                markerLine = i + 1;
                i++;
                continue;
            }

            if (string.IsNullOrWhiteSpace(line))
            {
                i++;
                continue;
            }

            var heading = HeadingPattern.Match(line);
            if (heading.Success)
            {
                RequireNoPendingMarker("a heading", i + 1);
                section = heading.Groups["text"].Value.Trim();
                i++;
                continue;
            }

            if (LooksLikeResultLabel(line))
            {
                throw new InvalidOperationException(
                    $"tutorial.md line {i + 1}: result label '{line.Trim()}' is not attached to a source fence — "
                    + "a claim must directly follow the fence it documents (blank lines allowed).");
            }

            RequireNoPendingMarker("ordinary prose", i + 1);
            i++;
        }

        RequireNoPendingMarker("the end of the file", lines.Length);
        // The repository corpus is cached for the test process. Returning the
        // mutable List behind IReadOnlyList would let one test cast it back,
        // alter the shared oracle, and change every later test's census.
        return examples.AsReadOnly();
    }

    /// <summary>
    /// Consumes a fence body starting at the opening line index; returns the
    /// index just past the closing <c>```</c> line.
    /// </summary>
    private static int ConsumeFenceBody(string[] lines, int openIndex, int fenceLine, out string body)
    {
        var j = openIndex + 1;
        while (j < lines.Length && !lines[j].StartsWith("```", StringComparison.Ordinal))
            j++;
        if (j >= lines.Length)
            throw new InvalidOperationException($"tutorial.md line {fenceLine}: unterminated fence.");
        if (lines[j] != "```")
        {
            throw new InvalidOperationException(
                $"tutorial.md line {j + 1}: malformed fence close '{lines[j].Trim()}' — the closing line must be "
                + "exactly ```.");
        }

        body = string.Join("\n", lines[(openIndex + 1)..j]);
        return j + 1;
    }

    private static int SkipBlanks(string[] lines, int index)
    {
        while (index < lines.Length && string.IsNullOrWhiteSpace(lines[index]))
            index++;
        return index;
    }

    /// <summary>
    /// Recognizes both canonical result labels and label-like near misses. The
    /// canonical regexes still decide what is supported; this wider lint gate
    /// only ensures that indentation, Markdown container prefixes, casing, or
    /// moved emphasis punctuation cannot silently turn a claim into prose.
    /// </summary>
    private static bool LooksLikeResultLabel(string line) =>
        ResultLabelCandidatePattern.IsMatch(line);
}
