using System.Globalization;
using KatLang;

namespace KatLang.ParserFuzz;

/// <summary>Which line-ending and preservation relations ran for a case, and why the others did not.</summary>
internal sealed record Utf16RelationOutcome(IReadOnlyList<string> Checked, IReadOnlyList<string> Skipped)
{
    public static readonly Utf16RelationOutcome None = new([], []);

    /// <summary>Stable one-field summary for the fingerprint.</summary>
    public string Summary => Checked.Count == 0 ? "none" : string.Join('+', Checked);
}

/// <summary>
/// Trusted relations between two physical encodings of ONE assembled source, plus exact-preservation
/// checks for language strings.
///
/// <para>Each relation states a property of the CURRENT documented contract and names the
/// precondition that makes it true. Where the contract deliberately differs between encodings — a
/// lone CR is not a line break — the relation pins the DIVERGENCE instead of asserting equivalence,
/// because asserting equality there would be a false relation, not a stronger test.</para>
/// </summary>
internal static class Utf16Relations
{
    public const string CrTransparency = "cr-transparency";
    public const string LoneCrNotALineBreak = "lone-cr-not-a-line-break";
    public const string TrailingNewlineNeutral = "trailing-newline-neutral";
    public const string ExactStringPreservation = "exact-string-preservation";

    public static Utf16RelationOutcome Check(Utf16Parameters parameters, ref Utf16Phase phase)
    {
        ArgumentNullException.ThrowIfNull(parameters);

        var ran = new List<string>(4);
        var skipped = new List<string>(4);

        phase = Utf16Phase.LineEndingRelation;
        var lf = Utf16SourceBuilder.BuildWithLineEndings(parameters, Utf16LineEndingMode.Lf);

        // Every line-ending relation compares two encodings of the SAME assembled text, so a case
        // whose own code units already contain a CR has no "LF encoding" to compare against.
        if (lf.Source.Contains('\r', StringComparison.Ordinal))
        {
            skipped.Add("source-supplies-its-own-cr");
        }
        else
        {
            CheckCrTransparency(parameters, lf);
            ran.Add(CrTransparency);

            if (lf.Source.Contains('\n', StringComparison.Ordinal))
            {
                CheckLoneCrIsNotALineBreak(parameters);
                ran.Add(LoneCrNotALineBreak);
            }
            else
            {
                skipped.Add("no-line-break-to-re-encode");
            }
        }

        phase = Utf16Phase.LineEndingRelation;
        if (TryCheckTrailingNewlineNeutral(parameters, out var trailingSkip)) ran.Add(TrailingNewlineNeutral);
        else skipped.Add(trailingSkip);

        phase = Utf16Phase.StringBridge;
        if (TryCheckExactStringPreservation(parameters, out var bridgeSkip)) ran.Add(ExactStringPreservation);
        else skipped.Add(bridgeSkip);

        return new Utf16RelationOutcome(ran, skipped);
    }

    /// <summary>
    /// LF versus CRLF. A <c>'\r'</c> advances neither the line nor the column and is consumed as
    /// whitespace, and every token scan already terminates at a <c>'\n'</c> — so inserting a
    /// <c>'\r'</c> immediately before each <c>'\n'</c> cannot change any token's text, length, line
    /// or column, nor any diagnostic. Offsets DO shift, and are deliberately not compared.
    /// </summary>
    private static void CheckCrTransparency(Utf16Parameters parameters, Utf16Case lf)
    {
        var crlf = Utf16SourceBuilder.BuildWithLineEndings(parameters, Utf16LineEndingMode.Crlf);

        var (lfTokens, _) = Lexer.Tokenize(lf.Source);
        var (crlfTokens, _) = Lexer.Tokenize(crlf.Source);

        if (lfTokens.Count != crlfTokens.Count)
            throw new Utf16InvariantException(
                $"{CrTransparency}: LF produced {Num(lfTokens.Count)} tokens, CRLF produced {Num(crlfTokens.Count)}.");

        for (var i = 0; i < lfTokens.Count; i++)
        {
            var a = lfTokens[i];
            var b = crlfTokens[i];
            if (a.Kind != b.Kind || a.Line != b.Line || a.Column != b.Column || a.Length != b.Length
                || !string.Equals(a.StringValue, b.StringValue, StringComparison.Ordinal))
            {
                throw new Utf16InvariantException(
                    $"{CrTransparency}: token {Num(i)} differs between LF and CRLF. " +
                    $"LF=[{a.Kind} ({Num(a.Line)},{Num(a.Column)}) len {Num(a.Length)}] " +
                    $"CRLF=[{b.Kind} ({Num(b.Line)},{Num(b.Column)}) len {Num(b.Length)}]");
            }
        }

        var lfSyntax = Parser.ParseSyntax(lf.Source);
        var crlfSyntax = Parser.ParseSyntax(crlf.Source);
        RequireSameDiagnostics(CrTransparency, lfSyntax.Diagnostics, crlfSyntax.Diagnostics);

        var lfPrint = FrontEndFingerprint.ComputeParseResult(lfSyntax.Root, lfSyntax.Diagnostics);
        var crlfPrint = FrontEndFingerprint.ComputeParseResult(crlfSyntax.Root, crlfSyntax.Diagnostics);
        if (!string.Equals(lfPrint, crlfPrint, StringComparison.Ordinal))
            throw new Utf16InvariantException(
                $"{CrTransparency}: LF and CRLF produced different syntax trees.\n  LF:   {lfPrint}\n  CRLF: {crlfPrint}");
    }

    /// <summary>
    /// LF versus a lone CR. KatLang's line boundary is <c>'\n'</c> ONLY, so re-encoding every break
    /// as a lone CR must collapse the source to a single line — this pins the divergence rather than
    /// claiming an equivalence the language does not have.
    /// </summary>
    private static void CheckLoneCrIsNotALineBreak(Utf16Parameters parameters)
    {
        var cr = Utf16SourceBuilder.BuildWithLineEndings(parameters, Utf16LineEndingMode.LoneCr);
        if (cr.Source.Contains('\n', StringComparison.Ordinal))
            throw new Utf16InvariantException(
                $"{LoneCrNotALineBreak}: the lone-CR encoding still contains a line feed; the builder is wrong.");

        var (tokens, _) = Lexer.Tokenize(cr.Source);
        foreach (var token in tokens)
        {
            if (token.Line != 1)
                throw new Utf16InvariantException(
                    $"{LoneCrNotALineBreak}: token {token.Kind} is on line {Num(token.Line)} of a source with no " +
                    "line feed — a carriage return was treated as a line break.");
        }

        var syntax = Parser.ParseSyntax(cr.Source);
        foreach (var diagnostic in syntax.Diagnostics)
        {
            if (diagnostic.Span is null) continue;
            if (diagnostic.Span.StartLineNumber != 1 || diagnostic.Span.EndLineNumber != 1)
                throw new Utf16InvariantException(
                    $"{LoneCrNotALineBreak}: diagnostic span {SourceSpanValidator.Describe(diagnostic.Span)} leaves " +
                    $"line 1 in a source with no line feed. Message: {Printable(diagnostic.Message)}");
        }
    }

    /// <summary>
    /// A trailing physical newline after a CLOSED, diagnostic-free program adds no content, so the
    /// syntax tree — spans included — must be unchanged. Deliberately not applied to unterminated
    /// constructs or to a comment that runs to end of file, where the newline is semantically real.
    /// </summary>
    private static bool TryCheckTrailingNewlineNeutral(Utf16Parameters parameters, out string skipReason)
    {
        var template = Utf16Tables.TemplateOf(parameters.Template);
        if (!template.ClosedWhenBenign)
        {
            skipReason = "template-is-not-a-closed-program";
            return false;
        }

        var without = Utf16SourceBuilder.BuildWithLineEndings(parameters, Utf16LineEndingMode.NoTrailingNewline);
        var withNewline = Utf16SourceBuilder.BuildWithLineEndings(parameters, Utf16LineEndingMode.TrailingNewline);

        var baseline = Parser.ParseSyntax(without.Source);
        if (baseline.Diagnostics.Count != 0)
        {
            skipReason = "case-does-not-parse-cleanly";
            return false;
        }

        var extended = Parser.ParseSyntax(withNewline.Source);
        RequireSameDiagnostics(TrailingNewlineNeutral, baseline.Diagnostics, extended.Diagnostics);

        var before = FrontEndFingerprint.ComputeParseResult(baseline.Root, baseline.Diagnostics);
        var after = FrontEndFingerprint.ComputeParseResult(extended.Root, extended.Diagnostics);
        if (!string.Equals(before, after, StringComparison.Ordinal))
            throw new Utf16InvariantException(
                $"{TrailingNewlineNeutral}: appending a newline to a closed program changed its syntax tree.\n" +
                $"  without: {before}\n  with:    {after}");

        skipReason = "";
        return true;
    }

    /// <summary>
    /// A valid string literal must reach the evaluator as EXACTLY the code units written between the
    /// quotes — no normalization, no replacement character, and a <c>Length</c> that counts UTF-16
    /// code units. This is the only path in the UTF-16 target that evaluates anything, and it runs
    /// only for a closed, diagnostic-free, single-literal program.
    /// </summary>
    private static bool TryCheckExactStringPreservation(Utf16Parameters parameters, out string skipReason)
    {
        var template = Utf16Tables.TemplateOf(parameters.Template);
        if (!template.StringBridge)
        {
            skipReason = "template-has-no-string-literal";
            return false;
        }

        if (parameters.ExecutionMode != Utf16ExecutionMode.StringBridge)
        {
            skipReason = "execution-mode-does-not-evaluate";
            return false;
        }

        var testCase = Utf16SourceBuilder.Build(parameters);
        var source = testCase.Source;

        var open = source.IndexOf('\'', StringComparison.Ordinal);
        var close = source.LastIndexOf('\'');
        if (open < 0 || close <= open)
        {
            skipReason = "no-terminated-string-literal";
            return false;
        }

        var expected = source[(open + 1)..close];
        if (expected.Contains('\'', StringComparison.Ordinal)
            || expected.Contains('\n', StringComparison.Ordinal)
            || expected.Contains('\r', StringComparison.Ordinal))
        {
            skipReason = "literal-content-would-end-the-literal";
            return false;
        }

        if (Parser.ParseSyntax(source).Diagnostics.Count != 0)
        {
            skipReason = "case-does-not-parse-cleanly";
            return false;
        }

        var run = KatLangEngine.Run(source);
        if (run is not RunResult.Success success)
        {
            skipReason = "program-did-not-evaluate-to-a-value";
            return false;
        }

        if (success.Value is not Result.Str actual)
        {
            skipReason = "program-did-not-produce-a-string";
            return false;
        }

        if (!string.Equals(actual.Value, expected, StringComparison.Ordinal))
            throw new Utf16InvariantException(
                $"{ExactStringPreservation}: the language string is not the literal's exact code units.\n" +
                $"  source:   {HexOf(expected)}\n  evaluated:{HexOf(actual.Value)}");

        if (actual.Value.Length != expected.Length)
            throw new Utf16InvariantException(
                $"{ExactStringPreservation}: string length is {Num(actual.Value.Length)} UTF-16 code units, " +
                $"the literal has {Num(expected.Length)}.");

        skipReason = "";
        return true;
    }

    private static void RequireSameDiagnostics(
        string relation, IReadOnlyList<Diagnostic> left, IReadOnlyList<Diagnostic> right)
    {
        if (left.Count != right.Count)
            throw new Utf16InvariantException(
                $"{relation}: diagnostic counts differ ({Num(left.Count)} vs {Num(right.Count)}).");

        for (var i = 0; i < left.Count; i++)
        {
            var a = left[i];
            var b = right[i];
            var sameSpan = a.Span is null
                ? b.Span is null
                : b.Span is not null
                  && a.Span.StartLineNumber == b.Span.StartLineNumber && a.Span.StartColumn == b.Span.StartColumn
                  && a.Span.EndLineNumber == b.Span.EndLineNumber && a.Span.EndColumn == b.Span.EndColumn;

            if (a.Severity != b.Severity
                || !string.Equals(a.Message, b.Message, StringComparison.Ordinal)
                || !sameSpan)
            {
                throw new Utf16InvariantException(
                    $"{relation}: diagnostic {Num(i)} differs.\n" +
                    $"  left:  {a.Severity} {SourceSpanValidator.Describe(a.Span)} {Printable(a.Message)}\n" +
                    $"  right: {b.Severity} {SourceSpanValidator.Describe(b.Span)} {Printable(b.Message)}");
            }
        }
    }

    /// <summary>Diagnostic messages may quote an isolated surrogate; keep reports well-formed.</summary>
    private static string Printable(string text)
    {
        var builder = new System.Text.StringBuilder(text.Length);
        foreach (var c in text) builder.Append(c is >= ' ' and <= '~' ? c : '?');
        return builder.ToString();
    }

    private static string HexOf(string text) => Utf16CodeUnits.ToHex(Utf16CodeUnits.FromString(text));

    private static string Num(int value) => value.ToString(CultureInfo.InvariantCulture);
}
