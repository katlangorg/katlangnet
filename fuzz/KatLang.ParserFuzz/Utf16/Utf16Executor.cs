using System.Globalization;
using KatLang;

namespace KatLang.ParserFuzz;

/// <summary>The stage the UTF-16 harness was executing, so a thrown exception names its culprit.</summary>
internal enum Utf16Phase
{
    Build,
    Lex,
    TokenInvariants,
    ParseSyntax,
    RawInvariants,
    DiagnosticBounds,
    FrontEnd,
    PublicParse,
    Determinism,
    LineEndingRelation,
    StringBridge,
}

/// <summary>Thrown when the UTF-16 harness observes a violated invariant or relation.</summary>
internal sealed class Utf16InvariantException(string message) : Exception(message);

/// <summary>What one processing of one source produced, in stable structural buckets.</summary>
internal sealed record Utf16Observation(
    int SourceLength,
    int LineCount,
    int TokenCount,
    int BadTokenCount,
    int CommentTokenCount,
    int StringTokenCount,
    int IdentifierTokenCount,
    int NumberTokenCount,
    int RawDiagnosticCount,
    int MaxDiagnosticsAtOnePosition,
    string FirstDiagnosticBucket,
    int MaxSpanEndLine,
    bool AnyMultilineSpan,
    bool AnyZeroWidthSpan,
    int FrontEndDiagnosticCount,
    bool FrontEndRan,
    string Fingerprint);

/// <summary>
/// Runs a UTF-16 case through the real lexer, parser and front end, and checks the invariants that
/// are specific to UTF-16 source text. Everything the existing raw-parser and frontend layers
/// already guarantee is checked by CALLING those layers (<see cref="FuzzInvariants"/>,
/// <see cref="FrontEndInvariants"/>) rather than restating their rules here.
///
/// <para>The invariants this layer adds are all about the code-unit/line/column model:</para>
/// <list type="number">
///   <item>the token stream covers the source, strictly advancing, ending at EOF — forward progress;</item>
///   <item>no token slice contains a line break, so columns and lengths cannot disagree;</item>
///   <item>every token's recorded (line, column) equals the offset-derived one — the lexer's
///         incremental bookkeeping cross-checked against the source;</item>
///   <item>token text is the exact source slice — no normalization, no replacement character;</item>
///   <item>diagnostics are bounded relative to source length, and bounded at any one position.</item>
/// </list>
/// </summary>
internal static class Utf16Executor
{
    /// <summary>
    /// Structural ceiling on total diagnostics, relative to source length. Every lexer diagnostic
    /// costs at least one code unit (a bad character, an unterminated string, an unparsable number)
    /// and the parser reports at bounded recovery points, so the count is linear in the source.
    /// Measured worst ratio over the whole stratified space is reported by the readiness test; this
    /// is set well above it so only a genuinely unbounded report can trip it.
    /// </summary>
    public const int DiagnosticsPerCodeUnit = 4;

    public const int DiagnosticsConstant = 32;

    /// <summary>
    /// Ceiling on diagnostics sharing ONE (line, column).
    ///
    /// <para>The bound is the parser's OWN nesting guard, and that is the whole justification.
    /// Diagnostics stack at one position when nested constructs are left open: each open level
    /// reports "expected the closer" at end of file, so <c>[[[[</c> reports once per bracket, all at
    /// the same place. That is not a stalled recovery — every code unit is consumed — so a bound
    /// derived from "the parser must make progress" would be measuring the wrong thing, and a small
    /// number picked from templates that never nest would simply be wrong (an early version used 16
    /// and a five-minute campaign refuted it in 14,090 executions). One diagnostic per open
    /// construct, and open constructs are capped by <see cref="Parser.MaxNestingDepth"/>: exceeding
    /// that means reporting is no longer tied to structure.</para>
    ///
    /// <para>Forward progress itself is established structurally by <see cref="CheckTokens"/> —
    /// strictly increasing token offsets ending at the source length — which needs no wall-clock
    /// measurement and does not confuse nesting with stalling.</para>
    /// </summary>
    public const int MaxDiagnosticsAtOnePosition = Parser.MaxNestingDepth;

    /// <summary>An unrelated program processed between two runs of the same source (A/B/A).</summary>
    private const string ProbeSourceB = "p, q = (1, 2)\nHelper(x) = x + p\nHelper(q)";

    public static Utf16Observation Execute(Utf16Case testCase, ref Utf16Phase phase)
    {
        ArgumentNullException.ThrowIfNull(testCase);
        var source = testCase.Source;

        phase = Utf16Phase.Lex;
        var (tokens, lexDiagnostics) = Lexer.Tokenize(source);

        phase = Utf16Phase.TokenInvariants;
        CheckTokens(source, tokens);

        phase = Utf16Phase.ParseSyntax;
        var syntax = Parser.ParseSyntax(source);

        phase = Utf16Phase.RawInvariants;
        FuzzInvariants.Check(source, syntax);

        phase = Utf16Phase.DiagnosticBounds;
        CheckLexerDiagnosticsSurvive(lexDiagnostics, syntax.Diagnostics);
        CheckDiagnosticBounds(source, syntax.Diagnostics);

        var frontEndDiagnostics = 0;
        var frontEndRan = false;
        if (testCase.Parameters.ExecutionMode != Utf16ExecutionMode.ParseSyntax)
        {
            phase = Utf16Phase.FrontEnd;
            var frontEndPhase = FrontEndPhase.RawParse;
            FrontEndInvariants.Run(source, ref frontEndPhase);

            var frontEnd = FrontEndPipeline.Process(source);
            frontEndDiagnostics = frontEnd.Diagnostics.Count;
            frontEndRan = true;
            CheckDiagnosticBounds(source, frontEnd.Diagnostics);
        }

        if (testCase.Parameters.ExecutionMode == Utf16ExecutionMode.EngineParse)
        {
            phase = Utf16Phase.PublicParse;
            var parsed = Parser.Parse(source);
            CheckDiagnosticBounds(source, parsed.Diagnostics);
        }

        return Observe(source, tokens, syntax, frontEndDiagnostics, frontEndRan);
    }

    /// <summary>
    /// Every lexer diagnostic must reach the parse result unchanged, in order, at the front.
    /// This is the same prefix guarantee <see cref="FrontEndInvariants"/> enforces one layer up,
    /// applied one layer down: a message naming an isolated surrogate is exactly the kind of thing
    /// that could be dropped or rewritten on the way out without anything else noticing.
    /// </summary>
    private static void CheckLexerDiagnosticsSurvive(
        IReadOnlyList<Diagnostic> lexer, IReadOnlyList<Diagnostic> syntax)
    {
        if (syntax.Count < lexer.Count)
            throw new Utf16InvariantException(
                $"The parser kept {Num(syntax.Count)} diagnostics but the lexer produced {Num(lexer.Count)}.");

        for (var i = 0; i < lexer.Count; i++)
        {
            var a = lexer[i];
            var b = syntax[i];
            if (a.Severity != b.Severity
                || !string.Equals(a.Message, b.Message, StringComparison.Ordinal)
                || a.Span != b.Span)
            {
                throw new Utf16InvariantException(
                    $"Lexer diagnostic {Num(i)} is not preserved as a parse-result prefix: " +
                    $"lexer=[{a.Severity}|{SourceSpanValidator.Describe(a.Span)}] " +
                    $"parser=[{b.Severity}|{SourceSpanValidator.Describe(b.Span)}]");
            }
        }
    }

    // ── Token invariants: the UTF-16 code-unit model ─────────────────────────

    /// <summary>Internal so the audit can run it over a deliberately doctored token stream and
    /// prove each violation is actually caught rather than merely believed to be.</summary>
    internal static void CheckTokens(string source, IReadOnlyList<Token> tokens)
    {
        if (tokens.Count == 0)
            throw new Utf16InvariantException("Lexer produced no tokens; the end-of-file token is mandatory.");

        for (var i = 0; i < tokens.Count; i++)
        {
            var token = tokens[i];
            var last = i == tokens.Count - 1;

            if (token.Kind == TokenKind.EndOfFile != last)
                throw new Utf16InvariantException(
                    $"End-of-file token placement is wrong at index {Num(i)} of {Num(tokens.Count)}: " +
                    $"kind={token.Kind}, last={last}.");

            if (token.Position < 0 || token.Length < 0)
                throw new Utf16InvariantException(
                    $"Token {Describe(token)} has a negative offset or length.");

            // Checked so an overflowing offset/length pair is a reported violation, never a wrap.
            int end;
            try { end = checked(token.Position + token.Length); }
            catch (OverflowException)
            {
                throw new Utf16InvariantException($"Token {Describe(token)} overflows int when its end is computed.");
            }

            if (end > source.Length)
                throw new Utf16InvariantException(
                    $"Token {Describe(token)} ends at {Num(end)}, past the {Num(source.Length)}-code-unit source.");

            if (!last)
            {
                if (token.Length < 1)
                    throw new Utf16InvariantException(
                        $"Token {Describe(token)} consumes no code units; the lexer would not advance.");

                if (token.Position >= tokens[i + 1].Position)
                    throw new Utf16InvariantException(
                        $"Token offsets do not strictly advance: {Describe(token)} then {Describe(tokens[i + 1])}. " +
                        "The lexer processed the same code-unit position twice.");
            }

            CheckTokenSlice(source, token, end);
            CheckTokenLocation(source, token, end, last);
        }

        var eof = tokens[^1];
        if (eof.Position != source.Length)
            throw new Utf16InvariantException(
                $"End-of-file token sits at {Num(eof.Position)}, not at the source end {Num(source.Length)}: " +
                "the lexer did not consume the whole source.");
        if (eof.Length != 0)
            throw new Utf16InvariantException($"End-of-file token has non-zero length {Num(eof.Length)}.");
    }

    /// <summary>
    /// Token text must be the exact source slice. Every lexer scan stops at a line break, so no
    /// token may contain one — that is what keeps <c>Column + Length</c> a valid end column.
    /// </summary>
    private static void CheckTokenSlice(string source, Token token, int end)
    {
        var slice = source[token.Position..end];

        if (token.Kind != TokenKind.EndOfFile && (slice.Contains('\n') || slice.Contains('\r')))
            throw new Utf16InvariantException(
                $"Token {Describe(token)} spans a line break, so its column arithmetic cannot be sound. " +
                $"Slice code units: {HexOf(slice)}");

        switch (token.Kind)
        {
            case TokenKind.Identifier when !string.Equals(token.StringValue, slice, StringComparison.Ordinal):
                throw new Utf16InvariantException(
                    $"Identifier token text is not its source slice: token={HexOf(token.StringValue ?? "")} " +
                    $"source={HexOf(slice)}");

            case TokenKind.Comment when !string.Equals(token.StringValue, slice[2..], StringComparison.Ordinal):
                throw new Utf16InvariantException(
                    $"Comment token text is not its source slice after '//': token={HexOf(token.StringValue ?? "")} " +
                    $"source={HexOf(slice[2..])}");

            case TokenKind.StringLiteral:
                {
                    // The lexer takes the value between the quotes; a terminated literal has both,
                    // an unterminated one only the opening quote. There are no escape sequences.
                    var terminated = slice.Length >= 2 && slice[^1] == '\'';
                    var expected = terminated ? slice[1..^1] : slice[1..];
                    if (!string.Equals(token.StringValue, expected, StringComparison.Ordinal))
                        throw new Utf16InvariantException(
                            $"String-literal value is not its exact source slice: token={HexOf(token.StringValue ?? "")} " +
                            $"source={HexOf(expected)} (terminated={terminated})");
                    break;
                }

            default:
                break;
        }
    }

    /// <summary>
    /// The lexer tracks (line, column) incrementally while scanning; this recomputes them from the
    /// token's recorded offset with the shared helper and requires agreement. Because no token
    /// contains a line break, the end position must also be exactly <c>Column + Length</c>.
    /// </summary>
    private static void CheckTokenLocation(string source, Token token, int end, bool last)
    {
        var (line, column) = SourceSpanValidator.LineColumnAt(source, token.Position);
        if (line != token.Line || column != token.Column)
            throw new Utf16InvariantException(
                $"Token {Describe(token)} records ({Num(token.Line)},{Num(token.Column)}) but its offset " +
                $"{Num(token.Position)} is at ({Num(line)},{Num(column)}).");

        if (last) return;

        var (endLine, endColumn) = SourceSpanValidator.LineColumnAt(source, end);
        if (endLine != token.Line || endColumn != token.Column + token.Length)
            throw new Utf16InvariantException(
                $"Token {Describe(token)} covers columns {Num(token.Column)}..{Num(token.Column + token.Length)} " +
                $"but its end offset {Num(end)} is at ({Num(endLine)},{Num(endColumn)}).");
    }

    // ── Diagnostic bounds ────────────────────────────────────────────────────

    private static void CheckDiagnosticBounds(string source, IReadOnlyList<Diagnostic> diagnostics)
    {
        var ceiling = checked((DiagnosticsPerCodeUnit * (source.Length + 1)) + DiagnosticsConstant);
        if (diagnostics.Count > ceiling)
            throw new Utf16InvariantException(
                $"{Num(diagnostics.Count)} diagnostics for a {Num(source.Length)}-code-unit source exceeds the " +
                $"structural ceiling of {Num(ceiling)}; reporting is not bounded by the source.");

        var (worst, at) = MaxAtOnePosition(diagnostics);
        if (worst > MaxDiagnosticsAtOnePosition)
            throw new Utf16InvariantException(
                $"{Num(worst)} diagnostics share position {at}, over the {Num(MaxDiagnosticsAtOnePosition)} " +
                "the parser's own nesting guard allows; reporting is no longer bounded by structure.");
    }

    private static (int Worst, string At) MaxAtOnePosition(IReadOnlyList<Diagnostic> diagnostics)
    {
        var counts = new Dictionary<(int, int), int>();
        var worst = 0;
        var at = "-";
        foreach (var diagnostic in diagnostics)
        {
            if (diagnostic.Span is null) continue;
            var key = (diagnostic.Span.StartLineNumber, diagnostic.Span.StartColumn);
            var next = counts.GetValueOrDefault(key) + 1;
            counts[key] = next;
            if (next > worst)
            {
                worst = next;
                at = $"({Num(key.Item1)},{Num(key.Item2)})";
            }
        }

        return (worst, at);
    }

    // ── Observation ──────────────────────────────────────────────────────────

    private static Utf16Observation Observe(
        string source,
        IReadOnlyList<Token> tokens,
        SyntaxParseResult syntax,
        int frontEndDiagnostics,
        bool frontEndRan)
    {
        var maxSpanEndLine = 1;
        var multiline = false;
        var zeroWidth = false;
        foreach (var diagnostic in syntax.Diagnostics)
        {
            if (diagnostic.Span is null) continue;
            maxSpanEndLine = Math.Max(maxSpanEndLine, diagnostic.Span.EndLineNumber);
            if (diagnostic.Span.EndLineNumber != diagnostic.Span.StartLineNumber) multiline = true;
            if (diagnostic.Span.EndLineNumber == diagnostic.Span.StartLineNumber
                && diagnostic.Span.EndColumn < diagnostic.Span.StartColumn + 1) zeroWidth = true;
        }

        var (worst, _) = MaxAtOnePosition(syntax.Diagnostics);

        return new Utf16Observation(
            SourceLength: source.Length,
            LineCount: SourceSpanValidator.LineWidths(source).Length,
            TokenCount: tokens.Count,
            BadTokenCount: tokens.Count(t => t.Kind == TokenKind.Bad),
            CommentTokenCount: tokens.Count(t => t.Kind == TokenKind.Comment),
            StringTokenCount: tokens.Count(t => t.Kind == TokenKind.StringLiteral),
            IdentifierTokenCount: tokens.Count(t => t.Kind == TokenKind.Identifier),
            NumberTokenCount: tokens.Count(t => t.Kind == TokenKind.Number),
            RawDiagnosticCount: syntax.Diagnostics.Count,
            MaxDiagnosticsAtOnePosition: worst,
            FirstDiagnosticBucket: Utf16Fingerprint.DiagnosticBucket(syntax.Diagnostics),
            MaxSpanEndLine: maxSpanEndLine,
            AnyMultilineSpan: multiline,
            AnyZeroWidthSpan: zeroWidth,
            FrontEndDiagnosticCount: frontEndDiagnostics,
            FrontEndRan: frontEndRan,
            Fingerprint: FrontEndFingerprint.ComputeParseResult(syntax.Root, syntax.Diagnostics));
    }

    /// <summary>The full structural result of one parse, used for the determinism comparisons.</summary>
    public static string StructuralDigest(string source)
    {
        var (tokens, _) = Lexer.Tokenize(source);
        var syntax = Parser.ParseSyntax(source);
        var digest = new System.Text.StringBuilder(512);
        digest.Append("tokens:").Append(tokens.Count).Append(';');
        foreach (var token in tokens)
            digest.Append(token.Kind).Append(':').Append(token.Position).Append(':')
                  .Append(token.Length).Append(':').Append(token.Line).Append(':').Append(token.Column).Append('|');
        digest.Append('\n').Append(FrontEndFingerprint.ComputeParseResult(syntax.Root, syntax.Diagnostics));
        return digest.ToString();
    }

    /// <summary>A/A and A/B/A: the same source must give the same structural digest, and an
    /// unrelated program processed between the two runs must not change it.</summary>
    public static void CheckDeterminism(string source)
    {
        var first = StructuralDigest(source);
        var second = StructuralDigest(source);
        if (!string.Equals(first, second, StringComparison.Ordinal))
            throw new Utf16InvariantException("Two parses of the same UTF-16 source produced different structural digests.");

        _ = StructuralDigest(ProbeSourceB);
        var third = StructuralDigest(source);
        if (!string.Equals(first, third, StringComparison.Ordinal))
            throw new Utf16InvariantException(
                "A UTF-16 source's structural digest changed after an unrelated source was parsed (leaked state).");
    }

    private static string Num(int value) => value.ToString(CultureInfo.InvariantCulture);

    private static string Describe(Token token)
        => $"[{token.Kind} @{Num(token.Position)}+{Num(token.Length)} ({Num(token.Line)},{Num(token.Column)})]";

    /// <summary>Hex code units — the only lossless printable form of possibly ill-formed text.</summary>
    private static string HexOf(string text)
        => Utf16CodeUnits.ToHex(Utf16CodeUnits.FromString(text));
}
