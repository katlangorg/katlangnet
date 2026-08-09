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
/// <b>Why a text scan and not an analyzer.</b> The dangerous construct is
/// syntactically distinctive, so a scan catches it with no false positives and
/// no new package dependency. It deliberately does not attempt full dataflow —
/// a test that stores the parse result and checks <c>HasErrors</c> itself is
/// correct and is not the pattern that caused the defect.
/// </para>
/// </summary>
public class SourceProvenanceEnforcementTests
{
    /// <summary>Matches `X.Parse(anything).Root` — the diagnostic-discarding shape.</summary>
    private static readonly Regex UnsafeParseRoot =
        new(@"Parse(?:Syntax)?\s*\([^;]*?\)\s*\.\s*Root", RegexOptions.Compiled);

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

    /// <summary>Lines that merely talk about the construct in prose.</summary>
    private static bool IsCommentary(string line)
    {
        var trimmed = line.TrimStart();
        return trimmed.StartsWith("//", StringComparison.Ordinal)
            || trimmed.StartsWith("///", StringComparison.Ordinal)
            || trimmed.StartsWith("*", StringComparison.Ordinal);
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
            for (var i = 0; i < lines.Length; i++)
            {
                if (IsCommentary(lines[i]))
                    continue;
                if (!UnsafeParseRoot.IsMatch(lines[i]))
                    continue;

                // `SourceProvenance.ParseValid(...).Root` and
                // `...ParseAllowingDiagnostics(...).Root` are the sanctioned forms.
                if (lines[i].Contains("ParseValid(", StringComparison.Ordinal)
                    || lines[i].Contains("ParseAllowingDiagnostics(", StringComparison.Ordinal))
                {
                    continue;
                }

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
        var files = TestSourceFiles().ToDictionary(Path.GetFileName, static path => path, StringComparer.Ordinal);

        foreach (var (name, reason) in PermissiveSites)
        {
            Assert.True(files.ContainsKey(name), $"Permissive allow-list names a missing file: {name}");
            Assert.False(string.IsNullOrWhiteSpace(reason), $"Permissive entry '{name}' has no reason.");

            var stillNeeded = File.ReadAllLines(files[name])
                .Any(line => !IsCommentary(line)
                    && UnsafeParseRoot.IsMatch(line)
                    && !line.Contains("ParseValid(", StringComparison.Ordinal)
                    && !line.Contains("ParseAllowingDiagnostics(", StringComparison.Ordinal));

            Assert.True(
                stillNeeded,
                $"Permissive allow-list entry '{name}' is stale — the file no longer takes a raw parse root. "
                + "Remove the entry so the rule applies there again.");
        }
    }

    /// <summary>
    /// The guard must actually detect the pattern it bans. This runs the real
    /// matcher over representative snippets rather than trusting the regex by
    /// inspection — a guard that silently stopped matching would be worse than
    /// no guard, because the suite would look protected.
    /// </summary>
    [Theory]
    [InlineData("        var ast = Parser.Parse(source).Root;", true)]
    [InlineData("        var root = Parser.Parse(\"1 + 2\").Root;", true)]
    [InlineData("        return new Expr.AlgorithmExpr(Parser.Parse(src).Root);", true)]
    [InlineData("        var r = Parser.ParseSyntax(source).Root;", true)]
    [InlineData("        var ast = SourceProvenance.ParseValid(source).Root;", false)]
    [InlineData("        var ast = SourceProvenance.ParseAllowingDiagnostics(source).Root;", false)]
    [InlineData("        var parsed = Parser.Parse(source);", false)]
    [InlineData("        Assert.False(parsed.HasErrors);", false)]
    public void GuardMatchesExactlyTheDiagnosticDiscardingShape(string line, bool expectedViolation)
    {
        var matches = !IsCommentary(line)
            && UnsafeParseRoot.IsMatch(line)
            && !line.Contains("ParseValid(", StringComparison.Ordinal)
            && !line.Contains("ParseAllowingDiagnostics(", StringComparison.Ordinal);

        Assert.Equal(expectedViolation, matches);
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
