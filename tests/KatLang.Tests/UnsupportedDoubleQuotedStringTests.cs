using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// STR-03 (November 2026): KatLang has ONE string literal form, raw single-quoted text. Double-quoted
/// strings and string interpolation were removed completely, so a double quote outside a comment or a
/// single-quoted string is rejected by ONE targeted lexical rule:
/// <list type="bullet">
///   <item>the run reaches from the double quote to the next double quote on the same physical line,
///   or to the end of that line; nothing inside it is interpreted (no escape, no brace, no hole);</item>
///   <item>it is ONE recovery <see cref="TokenKind.StringLiteral"/> token with the undecoded text, beside
///   exactly ONE <see cref="DiagnosticCode.UnsupportedDoubleQuotedString"/> diagnostic over the whole
///   run, never also <see cref="DiagnosticCode.UnterminatedStringLiteral"/>;</item>
///   <item>the parser builds a RECOVERY literal from it, so the rejected text can never become a module
///   URL: no <c>open</c> and no <c>load</c> downloads it, and the program is never evaluated.</item>
/// </list>
/// Lexing is implemented in C# only, so none of this has a Lean counterpart (the corpus cases are
/// parse-level, C#-only by construction). Expectations here were written from the rule, before the
/// implementation was run.
/// </summary>
public class UnsupportedDoubleQuotedStringTests
{
    private const string PlainMessage =
        "Double-quoted strings are not supported. Write text in single quotes: 'text'.";

    private const string InterpolationMessage =
        "Double-quoted strings and string interpolation are not supported. Write text in single quotes and give each value as a separate item: 'Total', x.";

    private static (IReadOnlyList<Token> Tokens, IReadOnlyList<Diagnostic> Diagnostics) Lex(string source)
    {
        var (tokens, diagnostics) = Lexer.Tokenize(source);
        Assert.Equal(TokenKind.EndOfFile, tokens[^1].Kind);
        return (tokens.Take(tokens.Count - 1).ToList(), diagnostics);
    }

    private static IReadOnlyList<Diagnostic> Unsupported(IEnumerable<Diagnostic> diagnostics)
        => diagnostics.Where(d => d.Code == DiagnosticCode.UnsupportedDoubleQuotedString).ToList();

    // ── The scanned run: one token, one diagnostic, the whole extent ─────────

    [Theory]
    [InlineData("\"abc\"", "abc")]
    [InlineData("\"\"", "")]                                  // empty double-quoted text
    [InlineData("\"it's\"", "it's")]                          // a single quote inside is text of the run
    [InlineData("\"# not a comment\"", "# not a comment")]    // and so is a comment marker
    [InlineData("\"a\\nb\\t\"", "a\\nb\\t")]              // nothing is decoded: backslash, n
    [InlineData("\"Total: {x}\"", "Total: {x}")]          // a former interpolation
    [InlineData("\"{{x}}\"", "{{x}}")]                // a former doubled-brace escape
    [InlineData("\"}\"", "}")]
    public void ATerminatedRun_IsOneRecoveryToken_AndOneDiagnosticOverBothQuotes(string source, string text)
    {
        var (tokens, diagnostics) = Lex(source);

        var token = Assert.Single(tokens);
        Assert.Equal(TokenKind.StringLiteral, token.Kind);
        Assert.Equal(text, token.StringValue);
        Assert.Equal((0, source.Length), (token.Position, token.Length));

        var diagnostic = Assert.Single(diagnostics);
        Assert.Equal(DiagnosticCode.UnsupportedDoubleQuotedString, diagnostic.Code);
        Assert.Equal(DiagnosticSeverity.Error, diagnostic.Severity);
        Assert.Equal(new SourceSpan(1, 1, 1, source.Length + 1), diagnostic.Span);
        Assert.Equal(token.Span, diagnostic.Span);
    }

    [Theory]
    [InlineData("\"abc\"", false)]
    [InlineData("\"\"", false)]
    [InlineData("\"a } b\"", false)]                          // a closing brace alone is not an opening one
    [InlineData("\"abc", false)]
    [InlineData("\"Total: {x}\"", true)]
    [InlineData("\"{\"", true)]
    [InlineData("\"a{b", true)]                                // unterminated, with an opening brace
    [InlineData("\"{{}}\"", true)]
    public void TheMessage_NamesInterpolation_ExactlyWhenTheRunHoldsAnOpeningBrace(string source, bool namesInterpolation)
    {
        var diagnostic = Assert.Single(Lex(source).Diagnostics);
        Assert.Equal(DiagnosticCode.UnsupportedDoubleQuotedString, diagnostic.Code);
        Assert.Equal(namesInterpolation ? InterpolationMessage : PlainMessage, diagnostic.Message);
    }

    [Theory]
    [InlineData("\"abc", 4, "abc")]
    [InlineData("\"", 1, "")]
    [InlineData("\"abc\nB = 2", 4, "abc")]                      // LF ends the run
    [InlineData("\"abc\r\nB = 2", 4, "abc")]                   // CRLF ends the run before the CR
    [InlineData("\"abc\rB = 2", 4, "abc")]                      // a lone CR ends it too
    [InlineData("\"a{x\n}\"", 4, "a{x")]                    // a hole never carries the run to the next line
    [InlineData("\"a\\", 3, "a\\")]                            // a trailing backslash escapes nothing
    public void AnUnterminatedRun_EndsAtItsPhysicalLine_AndIsThisDiagnosticAlone(string source, int length, string text)
    {
        var (tokens, diagnostics) = Lex(source);

        var token = tokens[0];
        Assert.Equal(TokenKind.StringLiteral, token.Kind);
        Assert.Equal((0, length), (token.Position, token.Length));
        Assert.Equal(text, token.StringValue);

        // The run's own diagnostic covers exactly the run and stops before the line break.
        var first = diagnostics[0];
        Assert.Equal(DiagnosticCode.UnsupportedDoubleQuotedString, first.Code);
        Assert.Equal(new SourceSpan(1, 1, 1, length + 1), first.Span);
        Assert.DoesNotContain(diagnostics, d => d.Code == DiagnosticCode.UnterminatedStringLiteral);

        // Nothing after the line break was consumed by the run: the next token starts after it.
        if (tokens.Count > 1)
            Assert.True(tokens[1].Position > length, $"token after the run starts at {tokens[1].Position}");
    }

    [Fact]
    public void TheNextLine_IsLexedAsOrdinaryCode_AfterAnUnterminatedRun()
    {
        foreach (var lineBreak in new[] { "\n", "\r\n" })
        {
            var (tokens, diagnostics) = Lex("A = \"abc" + lineBreak + "B = 2");

            Assert.Equal(
                [TokenKind.Identifier, TokenKind.Equals, TokenKind.StringLiteral, TokenKind.Identifier, TokenKind.Equals, TokenKind.Number],
                tokens.Select(t => t.Kind));
            Assert.Equal("abc", tokens[2].StringValue);
            Assert.Equal((2, 1, "B"), (tokens[3].Line, tokens[3].Column, tokens[3].StringValue));
            Assert.Equal(new SourceSpan(1, 5, 1, 9), Assert.Single(diagnostics).Span);
        }
    }

    [Fact]
    public void EveryRun_HasExactlyOneDiagnostic_AndScanningKnowsNoEscapes()
    {
        // Two runs, two diagnostics, each over its own run.
        var two = Lex("\"a\" + \"b\"");
        Assert.Equal(
            [TokenKind.StringLiteral, TokenKind.Plus, TokenKind.StringLiteral],
            two.Tokens.Select(t => t.Kind));
        Assert.Equal(
            [new SourceSpan(1, 1, 1, 4), new SourceSpan(1, 7, 1, 10)],
            two.Diagnostics.Select(d => Assert.NotNull(d.Span)));
        Assert.Equal(2, Unsupported(two.Diagnostics).Count);

        // A backslash escapes nothing, so `\"a \\\"b\\\" c\"` is the run `\"a \\\"`, the code `b\\`, and the
        // run `\" c\"`: two runs, two unsupported-quote diagnostics (and the stray backslash's own).
        var escaped = Lex("\"a \\\"b\\\" c\"");
        Assert.Equal(
            [(TokenKind.StringLiteral, "a \\"), (TokenKind.Identifier, "b"), (TokenKind.Bad, null), (TokenKind.StringLiteral, " c")],
            escaped.Tokens.Select(t => (t.Kind, t.StringValue)));
        Assert.Equal(2, Unsupported(escaped.Diagnostics).Count);
        Assert.Equal(DiagnosticCode.UnexpectedCharacter, Assert.Single(escaped.Diagnostics, d => d.Code != DiagnosticCode.UnsupportedDoubleQuotedString).Code);
    }

    // ── Where a double quote is ordinary text ────────────────────────────────

    [Theory]
    [InlineData("'say \"hi\"'", "say \"hi\"")]
    [InlineData("'\"'", "\"")]
    [InlineData("'{x}'", "{x}")]
    [InlineData("'C:\\temp'", "C:\\temp")]
    [InlineData("'\"Total: {x}\"'", "\"Total: {x}\"")]
    public void InsideASingleQuotedString_ADoubleQuoteABraceAndABackslashAreText(string source, string text)
    {
        var (tokens, diagnostics) = Lex(source);
        Assert.Empty(diagnostics);
        Assert.Equal(text, Assert.Single(tokens).StringValue);

        // ...and the literal is an ordinary one all the way to the value.
        var literal = Assert.IsType<Expr.StringLiteral>(Assert.Single(SourceProvenance.ParseValid(source).Root.Output));
        Assert.False(literal.IsRecoveryLiteral);
        Assert.Equal(new Result.Str(text), SourceProvenance.ParseValid(source).Evaluate().Value);
    }

    [Theory]
    [InlineData("1 # a \"comment\" with {x}")]
    [InlineData("# \"")]
    [InlineData("# \"unterminated\n2")]
    [InlineData("'a' # \"b\"\n'c'")]
    public void InsideAComment_ADoubleQuoteIsCommentText(string source)
    {
        var (tokens, diagnostics) = Lex(source);
        Assert.Empty(diagnostics);
        Assert.DoesNotContain(tokens, t => t.Kind == TokenKind.StringLiteral && source[t.Position] == '\"');
        Assert.False(Parser.Parse(source).HasErrors);
    }

    // ── The isolated expression: one diagnostic, no cascade ──────────────────

    [Theory]
    [InlineData("\"Total: {x}\"", 13)]
    [InlineData("\"Hello\"", 8)]
    [InlineData("\"{a, b}\"", 9)]            // a former multi-expression hole
    [InlineData("\"{}\"", 5)]                // a former empty hole
    [InlineData("\"{xs:0}\"", 9)]            // a former hole-level colon
    [InlineData("\"a\\qb\"", 7)]              // a former invalid escape
    [InlineData("\"Total: {x", 11)]            // a former unterminated hole
    public void AnIsolatedRejectedString_IsExactlyOneDiagnostic_ThroughTheWholeFrontEnd(string source, int endColumn)
    {
        foreach (var diagnostics in new[] { Parser.ParseSyntax(source).Diagnostics, Parser.Parse(source).Diagnostics })
        {
            var diagnostic = Assert.Single(diagnostics);
            Assert.Equal(DiagnosticCode.UnsupportedDoubleQuotedString, diagnostic.Code);
            Assert.Equal(new SourceSpan(1, 1, 1, endColumn), diagnostic.Span);
        }
    }

    // ── Recovery: a recovery literal, and later declarations as written ──────

    [Theory]
    [InlineData("A = \"abc\"\nB = 2\nB")]
    [InlineData("A = \"abc\nB = 2\nB")]                        // unterminated: the run ends with line 1
    [InlineData("A = \"a{b\nB = 2\nB")]
    [InlineData("A = \"abc\"\r\nB = 2\r\nB")]
    public void LaterDeclarations_AreParsedNormally(string source)
    {
        var provenance = SourceProvenance.ParseAllowingDiagnostics(source);

        var diagnostic = Assert.Single(provenance.Diagnostics);
        Assert.Equal(DiagnosticCode.UnsupportedDoubleQuotedString, diagnostic.Code);
        Assert.Equal(new SourcePosition(1, 5), Assert.NotNull(diagnostic.Span).Start);

        Assert.Equal(["A", "B"], provenance.Root.Properties.Select(p => p.Name));
        var a = Assert.IsType<Expr.StringLiteral>(Assert.Single(provenance.Root.Properties[0].Value.Output));
        Assert.True(a.IsRecoveryLiteral);
        Assert.Equal(2, Assert.IsType<Expr.Num>(Assert.Single(provenance.Root.Properties[1].Value.Output)).Value);
        Assert.Equal("B", Assert.IsType<Expr.Resolve>(Assert.Single(provenance.Root.Output)).Name);
    }

    /// <summary>The rejected text in each position a string could stand in: one diagnostic at the run, and the declaration after it intact.</summary>
    [Theory]
    [InlineData("call argument", "F(x) = x\nA = F(\"abc\")\nB = 2", 2, 7, 12)]
    [InlineData("list element", "A = [1, \"abc\", 3]\nB = 2", 1, 9, 14)]
    [InlineData("sequence item", "A = (1, \"abc\")\nB = 2", 1, 9, 14)]
    [InlineData("operand", "A = \"abc\" == 'abc'\nB = 2", 1, 5, 10)]
    [InlineData("clause-head pattern", "F(\"a\") = 1\nF(x) = 2\nB = 2", 1, 3, 6)]
    [InlineData("nested clause-head pattern", "F([\"a\", y]) = 1\nF(x) = 2\nB = 2", 1, 4, 7)]
    [InlineData("selector", "A = [1, 2][\"0\"]\nB = 2", 1, 12, 15)]
    [InlineData("dot receiver", "A = \"5\".string\nB = 2", 1, 5, 8)]
    public void InEveryPosition_TheRunIsTheOneDiagnostic_AndTheNextDeclarationSurvives(
        string position, string source, int line, int startColumn, int endColumn)
    {
        var provenance = SourceProvenance.ParseAllowingDiagnostics(source);

        var diagnostic = Assert.Single(provenance.Diagnostics);
        Assert.True(diagnostic.Code == DiagnosticCode.UnsupportedDoubleQuotedString, $"{position}: {diagnostic.Code} {diagnostic.Message}");
        Assert.Equal(new SourceSpan(line, startColumn, line, endColumn), diagnostic.Span);

        var b = Assert.Single(provenance.Root.Properties, p => p.Name == "B");
        Assert.Equal(2, Assert.IsType<Expr.Num>(Assert.Single(b.Value.Output)).Value);
        _ = SemanticModelBuilder.Build(provenance.Parsed);
    }

    [Fact]
    public void TheRecoveryLiteral_KeepsItsProvenanceThroughCopies_WithoutChangingStructuralEquality()
    {
        var provenance = SourceProvenance.ParseAllowingDiagnostics("\"https://katlang.org/a\"");
        Assert.True(provenance.HasFrontEndErrors);
        var literal = Assert.IsType<Expr.StringLiteral>(Assert.Single(provenance.Root.Output));
        Assert.True(literal.IsRecoveryLiteral);
        Assert.Equal("https://katlang.org/a", literal.Value);

        var copy = literal with { Span = null };
        Assert.True(copy.IsRecoveryLiteral);
        Assert.Equal(new Expr.StringLiteral(copy.Value), copy);
        Assert.Equal(new Expr.StringLiteral(copy.Value).GetHashCode(), copy.GetHashCode());
    }

    [Fact]
    public void RandomRunContent_NeverConsumesTheFollowingDeclaration_OrBreaksTheEditor()
    {
        // Whatever stands inside a run — openers that never close, closers that never opened, braces,
        // operators, keywords, a backslash, a single quote, a comment marker — the run is one token with
        // one diagnostic and ends with its line. Half of the samples close the run, half leave it open.
        var random = new Random(11112026);
        string[] pieces = ["(", ")", "[", "]", "{1}", "x", "1", ",", ":", "=", "+", "~", "open", "*", "@", "\\", "{", "}", "'", "#", "load("];
        for (var sample = 0; sample < 512; sample++)
        {
            var content = string.Join(" ", Enumerable.Range(0, 12).Select(_ => pieces[random.Next(pieces.Length)]));
            var terminated = sample % 2 == 0;
            var run = "\"" + content + (terminated ? "\"" : "");
            var source = "A = " + run + "\nB = 17\nB";

            var provenance = SourceProvenance.ParseAllowingDiagnostics(source);

            var diagnostic = Assert.Single(provenance.Diagnostics);
            Assert.True(diagnostic.Code == DiagnosticCode.UnsupportedDoubleQuotedString, source);
            Assert.Equal(new SourceSpan(1, 5, 1, 5 + run.Length), diagnostic.Span);
            Assert.Equal(["A", "B"], provenance.Root.Properties.Select(p => p.Name));
            var a = Assert.IsType<Expr.StringLiteral>(Assert.Single(provenance.Root.Properties[0].Value.Output));
            Assert.True(a.IsRecoveryLiteral);
            Assert.Equal(content, a.Value);
            Assert.Equal(17, Assert.IsType<Expr.Num>(Assert.Single(provenance.Root.Properties[1].Value.Output)).Value);
            _ = SemanticModelBuilder.Build(provenance.Parsed);
        }
    }

    // ── The semantic model: recovered text makes no sites ────────────────────

    [Fact]
    public void TheSemanticModel_BuildsOverRecoveredText_AndFabricatesNoSiteInsideTheRun()
    {
        const string source = "x = 5\n\"Total: {x}\"\ny = x + 1\ny";
        var provenance = SourceProvenance.ParseAllowingDiagnostics(source);
        Assert.Equal(DiagnosticCode.UnsupportedDoubleQuotedString, Assert.Single(provenance.Diagnostics).Code);

        var model = SemanticModelBuilder.Build(provenance.Parsed);

        // The `x` between the braces (line 2, column 10) is text of a rejected run, never a reference.
        Assert.Null(model.FindResolutionAt(new SourcePosition(2, 10)));
        Assert.DoesNotContain(model.IdentifierOccurrences, o => o.Span.Start.Line == 2);
        Assert.DoesNotContain(model.Declarations, d => d.Span.Start.Line == 2);

        // The code around it keeps its ordinary meaning.
        var reference = model.FindResolutionAt(new SourcePosition(3, 5));
        Assert.NotNull(reference);
        Assert.Equal("x", reference.Occurrence.Name);
        Assert.Equal(["x", "y"], model.Declarations.Select(d => d.Name).Order());
    }

    // ── Host actions: a rejected string never downloads, the program never runs ──

    public static TheoryData<string, DiagnosticCode> RejectedLoadTargets => new()
    {
        { "open \"https://katlang.org/lib.kat\"\nV", DiagnosticCode.UnsupportedDoubleQuotedString },
        { "open \"https://katlang.org/lib.kat", DiagnosticCode.UnsupportedDoubleQuotedString },
        { "open \"https://katlang.org/{x}.kat\"\nV", DiagnosticCode.UnsupportedDoubleQuotedString },
        { "open \"https://katlang.org/lib.kat\".Inner\nV", DiagnosticCode.UnsupportedDoubleQuotedString },
        { "open 'https://katlang.org/good.kat', \"https://katlang.org/lib.kat\"\nV", DiagnosticCode.UnsupportedDoubleQuotedString },
        { "M = load(\"https://katlang.org/lib.kat\")\nM.V", DiagnosticCode.UnsupportedDoubleQuotedString },
        { "M = load(\"https://katlang.org/lib.kat\n)\nM.V", DiagnosticCode.UnsupportedDoubleQuotedString },
        { "M = load(\"https://katlang.org/{x}.kat\")\nM.V", DiagnosticCode.UnsupportedDoubleQuotedString },
        { "F(0) = { open \"https://katlang.org/lib.kat\"\nV }\nF(0)", DiagnosticCode.UnsupportedDoubleQuotedString },
        { "F(0) = { M = load(\"https://katlang.org/lib.kat\")\nM.V }\nF(0)", DiagnosticCode.UnsupportedDoubleQuotedString },
        // The same structural refusal protects every recovered string token, of either quote kind.
        { "open 'https://katlang.org/lib.kat", DiagnosticCode.UnterminatedStringLiteral },
    };

    [Theory]
    [MemberData(nameof(RejectedLoadTargets))]
    public async Task ARejectedString_IsNeverADownloadTarget(string source, DiagnosticCode code)
    {
        const string rejected = "https://katlang.org/lib.kat";
        foreach (var diagnosticCapacity in new[] { 1, 2, 1000 })
        {
            var requests = new List<string>();
            var options = new RunOptions
            {
                SourceProcessingLimits = new() { MaxDiagnosticCount = diagnosticCapacity },
                DownloadCode = async (url, _) =>
                {
                    await Task.Yield();
                    requests.Add(url);
                    return "public V = 1";
                },
            };

            var parsed = await Parser.ParseAsync(source, options);

            Assert.True(parsed.HasErrors);
            Assert.Contains(parsed.Diagnostics, d => d.Code == code);
            // The refusal is structural: it holds whatever the diagnostic list could store.
            Assert.DoesNotContain(requests, url => url.StartsWith(rejected, StringComparison.Ordinal)
                || url.Contains("{x}", StringComparison.Ordinal));
            _ = SemanticModelBuilder.Build(parsed);

            // The engine neither downloads the rejected target nor evaluates the program.
            requests.Clear();
            var result = await KatLangEngine.RunAsync(source, options);
            Assert.IsType<RunResult.ParseFailure>(result);
            Assert.DoesNotContain(requests, url => url.StartsWith(rejected, StringComparison.Ordinal)
                || url.Contains("{x}", StringComparison.Ordinal));
        }
    }

    [Fact]
    public async Task TheRefusal_SurvivesDiagnosticOverflow_AndKeepsTheValidImports()
    {
        // One stored diagnostic: the `@` takes it, so the rejected run's own report is dropped —
        // and the run is still no download target, while the valid import beside it still loads.
        var requests = new List<string>();
        var parsed = await Parser.ParseAsync(
            "@\nopen \"https://katlang.org/bad.kat\", 'https://katlang.org/good.kat'\nV",
            new RunOptions
            {
                SourceProcessingLimits = new() { MaxDiagnosticCount = 1 },
                DownloadCode = (url, _) =>
                {
                    requests.Add(url);
                    return ValueTask.FromResult("public V = 1");
                },
            });

        Assert.True(parsed.HasErrors);
        Assert.Contains(parsed.Diagnostics, d => d.Code == DiagnosticCode.DiagnosticCountExceeded);
        Assert.DoesNotContain(parsed.Diagnostics, d => d.Code == DiagnosticCode.UnsupportedDoubleQuotedString);
        Assert.Equal(new[] { "https://katlang.org/good.kat" }, requests);
        _ = SemanticModelBuilder.Build(parsed);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task ARejectedTarget_InsideADownloadedModule_CannotTriggerASecondAcquisition(bool deferred)
    {
        var requests = new List<string>();
        var source = deferred
            ? "F(0) = { open 'https://katlang.org/outer.kat'\nV }\nF(0)"
            : "open 'https://katlang.org/outer.kat'\nV";
        var result = await KatLangEngine.RunAsync(source, new RunOptions
        {
            DownloadCode = async (url, _) =>
            {
                await Task.Yield();
                requests.Add(url);
                return "open \"https://katlang.org/inner.kat\"\npublic V = 1";
            },
        });

        Assert.Equal(new[] { "https://katlang.org/outer.kat" }, requests);
        if (deferred)
            Assert.IsType<RunResult.EvalFailure>(result);
        else
            Assert.IsType<RunResult.ParseFailure>(result);
    }

    [Theory]
    [InlineData("A = \"abc\"\nTouch()")]
    [InlineData("Touch()\n\"abc")]
    [InlineData("x = Touch()\n\"Total: {x}\"")]
    public async Task AProgramWithARejectedString_IsNotEvaluated_AndRunsNoHostOperation(string source)
    {
        var calls = 0;
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(HostOperation.Create("Touch", (_, _) =>
            {
                calls++;
                return new Result.Atom(1);
            })),
        };

        var sync = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source, options));
        var asynchronous = Assert.IsType<RunResult.ParseFailure>(await KatLangEngine.RunAsync(source, options));

        Assert.Equal(0, calls);
        Assert.Equal(KatLangErrorCode.UnsupportedDoubleQuotedString, Assert.Single(sync.Errors).Code);
        Assert.Equal(KatLangErrorCode.UnsupportedDoubleQuotedString, Assert.Single(asynchronous.Errors).Code);
    }

    // ── The public error ─────────────────────────────────────────────────────

    [Fact]
    public void TheDiagnostic_MapsToItsPublicErrorCode_WithStableNumbers()
    {
        Assert.Equal(63, (int)DiagnosticCode.UnsupportedDoubleQuotedString);
        Assert.Equal(85, (int)KatLangErrorCode.UnsupportedDoubleQuotedString);
        Assert.Equal(DiagnosticCode.UnsupportedDoubleQuotedString, Enum.GetValues<DiagnosticCode>().Max());
        Assert.Equal(KatLangErrorCode.UnsupportedDoubleQuotedString, Enum.GetValues<KatLangErrorCode>().Max());

        var failure = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run("x = 5\n\"Total: {x}\""));
        var error = Assert.Single(failure.Errors);
        Assert.Equal(KatLangErrorCode.UnsupportedDoubleQuotedString, error.Code);
        Assert.False(error.IsResourceLimit);
        Assert.Equal(InterpolationMessage, error.Message);
        Assert.Equal("[2:1] " + InterpolationMessage, error.ToString());
        Assert.Equal(error.ToString(), error.ToTerminalSafeString());

        var diagnostic = Assert.Single(Parser.Parse("\"abc\"").Diagnostics);
        var mapped = KatLangError.FromDiagnostic(diagnostic);
        Assert.Equal(KatLangErrorCode.UnsupportedDoubleQuotedString, mapped.Code);
        Assert.Equal("[1:1] " + PlainMessage, mapped.ToString());
    }

    // ── What STR-03 keeps: strings are ordinary values ───────────────────────

    [Theory]
    [InlineData("'{x}'", "{x}")]
    [InlineData("'C:\\temp'", "C:\\temp")]
    [InlineData("'say \"hi\"'", "say \"hi\"")]
    [InlineData("'a' == 'a', 'a' != 'b', 'a' == 'A', 'a' != 'a'", "true\ntrue\nfalse\nfalse")]
    [InlineData("Kind('x') = 1\nKind(y) = 2\nKind('x'), Kind('z'), Kind(5)", "1\n2\n2")]
    [InlineData("['a', 1], ('b', 2)", "[a, 1]\n(b, 2)")]
    [InlineData("1.50.string, 1.50.string == '1.50', 42.string == '42'", "1.50\ntrue\ntrue")]
    [InlineData("count(['a', 'b']), count('ab'), ['a', 'b'][1]", "2\n1\nb")]
    public void SingleQuotedStrings_KeepTheirSemantics(string source, string display)
    {
        var result = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));
        Assert.Equal(display, result.ToDisplayString().ReplaceLineEndings("\n"));
    }

    [Fact]
    public void NothingBuildsTextFromValues_SoANumberBesideAStringStaysANumber()
    {
        // `+` on strings stays a type error: there is no concatenation and no replacement for interpolation.
        var failure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run("'a' + 'b'"));
        Assert.Contains(failure.Errors, e => e.Code == KatLangErrorCode.TypeMismatch);

        // A sequence of a string and a number is two values of their own kinds, never one text.
        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run("Total = 3 + 8\n'Total', Total"));
        var items = Assert.IsType<Result.SequenceValue>(success.Value).Items;
        Assert.Equal([new Result.Str("Total"), new Result.Atom(11)], items);

        // So numeric display settings still reach the number.
        var shown = Assert.IsType<RunResult.Success>(KatLangEngine.Run("DisplayDecimals = 2\n'Total', 10 / 4"));
        Assert.Equal("Total\n2.50", shown.ToDisplayString().ReplaceLineEndings("\n"));
    }

    [Fact]
    public void HostCreatedStrings_AreValuesWhateverTheirText()
    {
        // A host-built literal and a host operation's result may hold text no written literal can:
        // a double quote, braces, a backslash, a line break. Nothing re-reads it as source.
        const string text = "say \"hi\" {x} C:\\temp\nline";

        var literal = Evaluator.Run(new Expr.StringLiteral(text));
        Assert.Equal(new Result.Str(text), literal.Value);

        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(HostOperation.Create("Text", (_, _) => new Result.Str(text))),
        };
        var fromHost = Assert.IsType<RunResult.Success>(KatLangEngine.Run("Text(), Text() == Text(), count(Text())", options));
        Assert.Equal(
            [new Result.Str(text), new Result.Bool(true), new Result.Atom(1)],
            Assert.IsType<Result.SequenceValue>(fromHost.Value).Items);
    }
}
