using System.Text.RegularExpressions;

namespace KatLang.Tests;

/// <summary>
/// Mechanical guard for the source-test provenance contract.
///
/// <para>
/// <b>The rule.</b> An ordinary source-language test must prove the front end
/// accepted its source before an evaluator result counts as evidence. The
/// construct <c>Parser.Parse(source).Root</c> silently discards
/// <c>ParseResult.Diagnostics</c>, so a test whose source KatLang REJECTS still
/// evaluates the parser's recovery tree and can pass for an unrelated reason.
/// Track 13 found 41 such tests in <c>EvaluatorTests</c> alone (3.2%), including
/// one named for an evaluator branch it never reached.
/// </para>
///
/// <para>
/// <b>What this enforces.</b> Taking <c>.Root</c> directly off a parse call is
/// banned in the test projects unless the site is listed in
/// <see cref="PermissiveSites"/> with an architectural reason. Legitimate strict
/// code goes through <see cref="SourceProvenance.ParseValid"/>; legitimate
/// permissive code goes through <see cref="SourceProvenance.ParseAllowingDiagnostics"/>
/// or is listed below.
/// </para>
///
/// <para>
/// <b>Why a text scan and not an analyzer.</b> The direct-call construct is
/// syntactically distinctive, and lightweight lexical masking keeps examples
/// in comments and strings from becoming false positives without adding a new
/// package dependency. This guard is deliberately line-based and does not
/// attempt full dataflow: stored parse results and calls split across lines
/// remain review concerns, while a stored result whose <c>HasErrors</c> is
/// checked before root consumption is valid.
/// </para>
/// </summary>
public class SourceProvenanceEnforcementTests
{
    /// <summary>
    /// Matches every diagnostic-discarding root-off-a-parse-call shape the
    /// suite's entry points expose today:
    /// <c>Parser.Parse(...).Root</c>, <c>Parser.ParseSyntax(...).Root</c> and
    /// its alias <c>.SyntaxRoot</c>, the async form
    /// <c>(await Parser.ParseAsync(...)).Root</c> (the lazy argument match
    /// absorbs the await group's closing paren) and its sync-over-async
    /// bypass <c>Parser.ParseAsync(...).Result.Root</c>, and the internal
    /// pipeline roots <c>FrontEndPipeline.Process(...).ElaboratedRoot</c> /
    /// <c>(await FrontEndPipeline.ProcessAsync(...)).ElaboratedRoot</c>
    /// (a chained <c>.ToParseResult().Root</c> included). <c>Process</c> is
    /// recognized only behind the <c>FrontEndPipeline</c> qualifier, so
    /// unrelated Process-named methods stay unmatched. The sanctioned strict
    /// helpers (<c>ParseValid</c>/<c>ParseValidAsync</c>/
    /// <c>ParseSyntaxValidRoot</c>/<c>ParseAllowingDiagnostics</c>...) never
    /// match: their names put an identifier character where this pattern
    /// requires the call's opening parenthesis.
    /// </summary>
    private static readonly Regex UnsafeParseRoot = new(
        @"(?:\bParser\s*\.\s*Parse(?:Syntax|Async)?|\bFrontEndPipeline\s*\.\s*Process(?:Async)?)"
        + @"\s*\([^;]*?\)(?:\s*\.\s*Result)?\s*\.\s*(?:Syntax|Elaborated)?Root",
        RegexOptions.Compiled | RegexOptions.CultureInvariant | RegexOptions.NonBacktracking);

    /// <summary>
    /// The one violation decision, shared by the scanner, the allow-list
    /// staleness check, and the recognizer self-tests below — the self-tests
    /// exercise the REAL matcher, never a re-composed copy of it.
    /// </summary>
    private static bool IsViolationLine(string line)
    {
        var lexicalState = new CSharpLexicalState();
        return IsViolationLine(line, lexicalState);
    }

    private static bool IsViolationLine(string line, CSharpLexicalState lexicalState)
        => UnsafeParseRoot.IsMatch(lexicalState.CodeOnly(line));

    /// <summary>
    /// Sites where consuming a parse root WITHOUT checking diagnostics is the
    /// point. Each entry needs an architectural reason; "it is old" is not one.
    /// Keyed by file name, with the reason recorded for review.
    /// </summary>
    private static readonly IReadOnlyDictionary<string, string> PermissiveSites =
        new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["EditorFuzzHarnessTests.cs"] =
                "ERROR-TOLERANT-TOOLING: the editor contract is defined ON malformed source "
                + "(unresolved load, recovery trees). Requiring a clean parse would delete the test.",
        };

    private static IReadOnlyList<string> TestSourceFiles()
    {
        var root = FindRepoRoot();
        return Directory
            .EnumerateFiles(Path.Combine(root, "tests"), "*.cs", SearchOption.AllDirectories)
            .Concat(Directory.Exists(Path.Combine(root, "fuzz"))
                ? Directory.EnumerateFiles(Path.Combine(root, "fuzz"), "*.cs", SearchOption.AllDirectories)
                : [])
            .Where(static path => !path.Contains($"{Path.DirectorySeparatorChar}obj{Path.DirectorySeparatorChar}", StringComparison.Ordinal)
                && !path.Contains($"{Path.DirectorySeparatorChar}bin{Path.DirectorySeparatorChar}", StringComparison.Ordinal))
            .OrderBy(static path => path, StringComparer.Ordinal)
            .ToList();
    }

    private static string FindRepoRoot()
    {
        var directory = new DirectoryInfo(AppContext.BaseDirectory);
        while (directory is not null && !File.Exists(Path.Combine(directory.FullName, "KatLang.slnx")))
            directory = directory.Parent;

        Assert.True(directory is not null, "Could not locate the repository root (KatLang.slnx).");
        return directory!.FullName;
    }

    /// <summary>
    /// Lightweight C# lexical masking for the line-based guard. Strings and
    /// comments become spaces before the root matcher runs, so examples in
    /// prose cannot be false positives. Block comments, verbatim strings, and
    /// raw strings retain state across lines; executable code after a closing
    /// block-comment/string delimiter remains visible. This is deliberately
    /// lexical rather than a Roslyn/dataflow analyzer — it only separates code
    /// from trivia for the distinctive direct-call shape enforced here.
    /// </summary>
    private sealed class CSharpLexicalState
    {
        private bool _inBlockComment;
        private bool _inVerbatimString;
        private int _rawStringDelimiterLength;

        public string CodeOnly(string line)
        {
            var code = line.ToCharArray();
            var index = 0;

            while (index < code.Length)
            {
                if (_inBlockComment)
                {
                    var close = line.IndexOf("*/", index, StringComparison.Ordinal);
                    if (close < 0)
                    {
                        Blank(code, index, code.Length);
                        break;
                    }

                    Blank(code, index, close + 2);
                    _inBlockComment = false;
                    index = close + 2;
                    continue;
                }

                if (_rawStringDelimiterLength != 0)
                {
                    var close = FindQuoteRun(line, index, _rawStringDelimiterLength);
                    if (close < 0)
                    {
                        Blank(code, index, code.Length);
                        break;
                    }

                    var closeEnd = close + QuoteRunLength(line, close);
                    Blank(code, index, closeEnd);
                    _rawStringDelimiterLength = 0;
                    index = closeEnd;
                    continue;
                }

                if (_inVerbatimString)
                {
                    var close = FindVerbatimStringEnd(line, index);
                    if (close < 0)
                    {
                        Blank(code, index, code.Length);
                        break;
                    }

                    Blank(code, index, close);
                    _inVerbatimString = false;
                    index = close;
                    continue;
                }

                if (index + 1 < code.Length && code[index] == '/' && code[index + 1] == '/')
                {
                    Blank(code, index, code.Length);
                    break;
                }

                if (index + 1 < code.Length && code[index] == '/' && code[index + 1] == '*')
                {
                    var start = index;
                    _inBlockComment = true;
                    index += 2;
                    var close = line.IndexOf("*/", index, StringComparison.Ordinal);
                    if (close < 0)
                    {
                        Blank(code, start, code.Length);
                        break;
                    }

                    Blank(code, start, close + 2);
                    _inBlockComment = false;
                    index = close + 2;
                    continue;
                }

                if (code[index] == '"')
                {
                    var quoteRunLength = QuoteRunLength(line, index);
                    if (quoteRunLength >= 3)
                    {
                        _rawStringDelimiterLength = quoteRunLength;
                        Blank(code, index, index + quoteRunLength);
                        index += quoteRunLength;
                        continue;
                    }

                    var start = index;
                    if ((index > 0 && code[index - 1] == '@')
                        || (index > 1 && code[index - 2] == '@' && code[index - 1] == '$'))
                    {
                        _inVerbatimString = true;
                        index++;
                        var close = FindVerbatimStringEnd(line, index);
                        if (close < 0)
                        {
                            Blank(code, start, code.Length);
                            break;
                        }

                        Blank(code, start, close);
                        _inVerbatimString = false;
                        index = close;
                        continue;
                    }

                    index = FindEscapedLiteralEnd(line, index + 1, '"');
                    Blank(code, start, index);
                    continue;
                }

                if (code[index] == '\'')
                {
                    var start = index;
                    index = FindEscapedLiteralEnd(line, index + 1, '\'');
                    Blank(code, start, index);
                    continue;
                }

                index++;
            }

            return new string(code);
        }

        private static int FindEscapedLiteralEnd(string line, int index, char delimiter)
        {
            var escaped = false;
            while (index < line.Length)
            {
                var current = line[index++];
                if (escaped)
                {
                    escaped = false;
                    continue;
                }
                if (current == '\\')
                {
                    escaped = true;
                    continue;
                }
                if (current == delimiter)
                    break;
            }
            return index;
        }

        private static int FindVerbatimStringEnd(string line, int index)
        {
            while (index < line.Length)
            {
                if (line[index] != '"')
                {
                    index++;
                    continue;
                }

                if (index + 1 < line.Length && line[index + 1] == '"')
                {
                    index += 2;
                    continue;
                }

                return index + 1;
            }
            return -1;
        }

        private static int FindQuoteRun(string line, int index, int minimumLength)
        {
            while (index < line.Length)
            {
                if (line[index] == '"' && QuoteRunLength(line, index) >= minimumLength)
                    return index;
                index++;
            }
            return -1;
        }

        private static int QuoteRunLength(string line, int index)
        {
            var end = index;
            while (end < line.Length && line[end] == '"')
                end++;
            return end - index;
        }

        private static void Blank(char[] code, int start, int endExclusive)
            => Array.Fill(code, ' ', start, endExclusive - start);
    }

    private sealed record Violation(string File, int Line, string Text);

    private static IReadOnlyList<Violation> Scan()
    {
        var violations = new List<Violation>();

        foreach (var path in TestSourceFiles())
        {
            var name = Path.GetFileName(path);
            if (PermissiveSites.ContainsKey(name))
                continue;

            // This file's own [InlineData] rows are the guard's self-test data,
            // and SourceProvenance.cs IS the sanctioned implementation — the one
            // place where a raw parse root is taken deliberately, behind an API
            // that forces callers to state their contract.
            if (name is "SourceProvenanceEnforcementTests.cs" or "SourceProvenance.cs")
                continue;

            var lines = File.ReadAllLines(path);
            var lexicalState = new CSharpLexicalState();
            for (var i = 0; i < lines.Length; i++)
            {
                if (IsViolationLine(lines[i], lexicalState))
                    violations.Add(new Violation(name, i + 1, lines[i].Trim()));
            }
        }

        return violations;
    }

    [Fact]
    public void NoTestTakesAParseRootWithoutEstablishingProvenance()
    {
        var violations = Scan();

        Assert.True(
            violations.Count == 0,
            "Source-test provenance violation: taking `.Root` off a parse call discards the front-end "
            + "diagnostics, so a test whose source KatLang rejects would still evaluate the recovery tree."
            + Environment.NewLine
            + "Use SourceProvenance.ParseValid(source) for ordinary source-language tests, "
            + "SourceProvenance.ExpectFrontEndError(source) when the parser/elaborator is the subject, or "
            + "SourceProvenance.ParseAllowingDiagnostics(source) when malformed source IS the subject."
            + Environment.NewLine + Environment.NewLine
            + string.Join(Environment.NewLine, violations.Select(v => $"  {v.File}:{v.Line}  {v.Text}")));
    }

    /// <summary>
    /// The allow-list must stay honest: an entry whose file no longer contains
    /// the construct is stale and hides the rule from that file for free.
    /// </summary>
    [Fact]
    public void EveryPermissiveExceptionIsStillNeeded()
    {
        var files = TestSourceFiles().ToDictionary(
            static path => Path.GetFileName(path)!,
            static path => path,
            StringComparer.Ordinal);

        foreach (var (name, reason) in PermissiveSites)
        {
            Assert.True(files.ContainsKey(name), $"Permissive allow-list names a missing file: {name}");
            Assert.False(string.IsNullOrWhiteSpace(reason), $"Permissive entry '{name}' has no reason.");

            var lexicalState = new CSharpLexicalState();
            var stillNeeded = File.ReadAllLines(files[name])
                .Any(line => IsViolationLine(line, lexicalState));

            Assert.True(
                stillNeeded,
                $"Permissive allow-list entry '{name}' is stale — the file no longer takes a raw parse root. "
                + "Remove the entry so the rule applies there again.");
        }
    }

    /// <summary>
    /// The guard must actually detect the pattern it bans. This runs the real
    /// matcher (<see cref="IsViolationLine"/>) over representative snippets
    /// rather than trusting the regex by inspection — a guard that silently
    /// stopped matching would be worse than no guard, because the suite would
    /// look protected. The rows cover every sanctioned root family: the sync
    /// parser roots, the raw-syntax root and its <c>SyntaxRoot</c> alias, the
    /// awaited async parser root (with and without options) plus its
    /// <c>.Result</c> sync-over-async bypass, and the internal
    /// <c>FrontEndPipeline</c> roots (sync, awaited async, and the chained
    /// <c>ToParseResult().Root</c> form). The negative rows pin against
    /// overmatching: parse calls whose result is stored or whose diagnostics
    /// are checked, the strict provenance helpers (async included), prose in
    /// comments, mere mentions of ParseAsync without a root, and
    /// Process-named methods outside the FrontEndPipeline qualifier.
    /// </summary>
    [Theory]
    [InlineData("        var ast = Parser.Parse(source).Root;", true)]
    [InlineData("        var root = Parser.Parse(\"1 + 2\").Root;", true)]
    [InlineData("        return new Expr.AlgorithmExpr(Parser.Parse(src).Root);", true)]
    [InlineData("        var r = Parser.ParseSyntax(source).Root;", true)]
    [InlineData("        var r = Parser.ParseSyntax(source).SyntaxRoot;", true)]
    [InlineData("        var root = (await Parser.ParseAsync(source)).Root;", true)]
    [InlineData("        var root = (await Parser.ParseAsync(source, options)).Root;", true)]
    [InlineData("        var root = Parser.ParseAsync(source).Result.Root;", true)]
    [InlineData("        var a = FrontEndPipeline.Process(source).ElaboratedRoot;", true)]
    [InlineData("        var a = FrontEndPipeline.Process(source, options).ElaboratedRoot;", true)]
    [InlineData("        var a = (await FrontEndPipeline.ProcessAsync(source, options)).ElaboratedRoot;", true)]
    [InlineData("        var r = FrontEndPipeline.Process(source).ToParseResult().Root;", true)]
    [InlineData("        var ast = SourceProvenance.ParseValid(source).Root;", false)]
    [InlineData("        var ast = SourceProvenance.ParseAllowingDiagnostics(source).Root;", false)]
    [InlineData("        var root = (await SourceProvenance.ParseValidAsync(source)).Root;", false)]
    [InlineData("        var provenance = await SourceProvenance.ParseValidAsync(source, options);", false)]
    [InlineData("        var syntaxRoot = SourceProvenance.ParseSyntaxValidRoot(source);", false)]
    [InlineData("        var parsed = Parser.Parse(source);", false)]
    [InlineData("        var parsed = await Parser.ParseAsync(source, options);", false)]
    [InlineData("        Assert.False((await Parser.ParseAsync(Source)).HasErrors);", false)]
    [InlineData("        var frontEnd = FrontEndPipeline.Process(source);", false)]
    [InlineData("        var done = loader.Process(request).Root;", false)]
    [InlineData("        var done = SomeOtherParser.ParseAsync(request).Root;", false)]
    [InlineData("        var s = \"see Parser.ParseAsync(x) for loading\";", false)]
    [InlineData("        var s = \"Parser.Parse(x).Root\";", false)]
    [InlineData("        var s = @\"Parser.ParseAsync(x).Result.Root\";", false)]
    [InlineData("        var s = @$\"see \"\"Parser.Parse(x).Root\"\"\";", false)]
    [InlineData("        var s = \"\"\"Parser.ParseAsync(x).Root\"\"\";", false)]
    [InlineData("        // var ast = Parser.Parse(source).Root; (prose about the banned shape)", false)]
    [InlineData("        /* var ast = Parser.Parse(source).Root; */", false)]
    [InlineData("        /* prose */ var ast = Parser.Parse(source).Root;", true)]
    [InlineData("        var ok = SourceProvenance.ParseValid(x).Root; var bad = Parser.Parse(y).Root;", true)]
    [InlineData("        Assert.False(parsed.HasErrors);", false)]
    public void GuardMatchesExactlyTheDiagnosticDiscardingShape(string line, bool expectedViolation)
        => Assert.Equal(expectedViolation, IsViolationLine(line));

    [Fact]
    public void Guard_BlockCommentState_DoesNotHideCodeAfterTheClosingDelimiter()
    {
        var lexicalState = new CSharpLexicalState();
        Assert.False(IsViolationLine("/* Parser.Parse(x).Root", lexicalState));
        Assert.True(IsViolationLine("*/ var root = Parser.Parse(y).Root;", lexicalState));
    }

    [Fact]
    public void Guard_LongNonMatchingLine_WithManyParserFragments_RemainsNonMatching()
    {
        // The production matcher uses RegexOptions.NonBacktracking, so this
        // adversarial row is structurally linear rather than one suffix scan
        // per ParseAsync fragment. No wall-clock assertion is needed.
        var line = string.Join(" + ", Enumerable.Repeat("Parser.ParseAsync(source)", 20_000));
        Assert.False(IsViolationLine(line));
    }

    // ── Strict-helper contract (Phase G) ──────────────────────────────────────

    /// <summary>
    /// <c>ParseValid</c> must FAIL on rejected source. If a future refactor made
    /// it permissive, every migrated call site would silently regress to the
    /// original defect while staying green.
    /// </summary>
    [Fact]
    public void ParseValid_FailsLoudlyOnFrontEndRejectedSource()
    {
        // `open` after a property is a parser error — the exact shape that hid
        // 35 vacuous tests.
        var failure = Record.Exception(() => SourceProvenance.ParseValid("A = { public X = 1 }\nopen A\nX"));

        Assert.NotNull(failure);
        Assert.Contains("clean front end", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ParseValid_ReturnsTheElaboratedRootForLegalSource()
    {
        var provenance = SourceProvenance.ParseValid("open A\nA = { public X = 1 }\nX");

        Assert.False(provenance.HasFrontEndErrors);
        Assert.Empty(provenance.Diagnostics);
        Assert.Contains(provenance.Root.Properties, p => p.Name == "A");
    }

    /// <summary>
    /// <c>ParseValidAsync</c> carries the same strict contract as
    /// <c>ParseValid</c> over the authoritative async front end.
    /// </summary>
    [Fact]
    public async Task ParseValidAsync_FailsLoudlyOnFrontEndRejectedSource()
    {
        var failure = await Record.ExceptionAsync(
            () => SourceProvenance.ParseValidAsync("A = { public X = 1 }\nopen A\nX"));

        Assert.NotNull(failure);
        Assert.Contains("clean front end", failure!.Message, StringComparison.Ordinal);
    }

    [Fact]
    public async Task ParseValidAsync_ElaboratesLoadingSourceThroughTheAsyncFrontEnd()
    {
        // `open 'url'` with a configured downloader is elaborable ONLY by the
        // asynchronous front end: the synchronous source-level entry points
        // reject a downloader-configured options object with
        // InvalidOperationException before parsing. That pins the helper to
        // the real async path — a quiet sync-parse reimplementation cannot
        // pass this test.
        var options = new RunOptions
        {
            DownloadCode = (_, _) => ValueTask.FromResult("public M = 41"),
        };

        var provenance = await SourceProvenance.ParseValidAsync(
            "open 'https://katlang.org/provenance/mod.kat'\nM + 1", options);

        Assert.False(provenance.HasFrontEndErrors);
        Assert.Empty(provenance.Diagnostics);

        var result = provenance.Evaluate();
        Assert.False(result.IsError);
        Assert.True(Result.ValueComparer.Equals(result.Value, new Result.Atom(42)));
    }

    /// <summary>The permissive helper must keep diagnostics observable, not swallow them.</summary>
    [Fact]
    public void ParseAllowingDiagnostics_PreservesDiagnostics()
    {
        var provenance = SourceProvenance.ParseAllowingDiagnostics("A = { public X = 1 }\nopen A\nX");

        Assert.True(provenance.HasFrontEndErrors);
        Assert.NotEmpty(provenance.Diagnostics);
        Assert.NotNull(provenance.Root);
    }

    [Fact]
    public void ExpectFrontEndError_FailsWhenTheFrontEndAcceptsTheSource()
    {
        Assert.NotNull(Record.Exception(() => SourceProvenance.ExpectFrontEndError("1 + 2")));
        Assert.NotEmpty(SourceProvenance.ExpectFrontEndError("A = { public X = 1 }\nopen A\nX"));
    }

    /// <summary>
    /// <c>ExpectEvaluationError&lt;T&gt;</c> must reject a DIFFERENT error type.
    /// Asserting only "something failed" is what let wrong-layer tests survive.
    /// </summary>
    [Fact]
    public void ExpectEvaluationError_IsTypeSpecific()
    {
        var provenance = SourceProvenance.ParseValid("F(0) = 1\nF(n) = 2\nF");

        Assert.IsType<EvalError.NoMatchingBranch>(provenance.ExpectEvaluationError());
        Assert.NotNull(Record.Exception(() => provenance.ExpectEvaluationError<EvalError.DivByZero>()));
    }
}
