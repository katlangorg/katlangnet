using System.Numerics;

namespace KatLang.Tests;

/// <summary>
/// The friend-side half of the Token construction contract (public API cleanup, Task 2,
/// September 2026): <see cref="Token"/> is a non-positional record whose construction is
/// internal — the lexer and the parser's recovery build tokens through the one internal
/// constructor and the seven kind-shaped factories, and friend tests may doctor a token
/// through <c>with</c>. These tests pin what the compiler cannot: every property is
/// carried by the constructor and by copies, record equality and hashing cover exactly
/// the seven token fields, each factory pairs its kind with its payload, and the lexer's
/// production tokens keep the payload rules the type documents. The non-friend half
/// (what a consumer can and cannot do) lives in the public API test project.
/// </summary>
public class TokenTests
{
    /// <summary>
    /// A token with EVERY field non-default — a state the lexer never emits (a number with
    /// text), chosen so that a constructor or copy that drops any one field is observable.
    /// </summary>
    private static Token Sample()
        => new(TokenKind.Number, position: 7, length: 3, line: 2, column: 5, numValue: 42, stringValue: "payload");

    [Fact]
    public void Constructor_CarriesEveryProperty()
    {
        var token = new Token(TokenKind.Identifier, position: 11, length: 4, line: 3, column: 9, numValue: 5, stringValue: "name");

        Assert.Equal(TokenKind.Identifier, token.Kind);
        Assert.Equal(11, token.Position);
        Assert.Equal(4, token.Length);
        Assert.Equal(3, token.Line);
        Assert.Equal(9, token.Column);
        Assert.Equal(5, token.NumValue);
        Assert.Equal("name", token.StringValue);

        // The payload parameters default to "no payload".
        var bare = new Token(TokenKind.Plus, 0, 1, 1, 1);
        Assert.Equal(default, bare.NumValue);
        Assert.Null(bare.StringValue);
    }

    [Fact]
    public void Equality_IsStructuralOverTheSevenFields()
    {
        var first = Sample();
        var second = new Token(TokenKind.Number, 7, 3, 2, 5, 42, "payload");

        Assert.NotSame(first, second);
        Assert.Equal(first, second);
        Assert.True(first == second);
        Assert.False(first != second);
        Assert.True(first.Equals((object)second));
        Assert.Equal(first.GetHashCode(), second.GetHashCode());
        Assert.False(first.Equals(null));
    }

    public static TheoryData<string, Func<Token, Token>> EachFieldChange => new()
    {
        { "Kind", t => t with { Kind = TokenKind.Identifier } },
        { "Position", t => t with { Position = t.Position + 1 } },
        { "Length", t => t with { Length = t.Length + 1 } },
        { "Line", t => t with { Line = t.Line + 1 } },
        { "Column", t => t with { Column = t.Column + 1 } },
        { "NumValue", t => t with { NumValue = t.NumValue + 1 } },
        { "StringValue", t => t with { StringValue = "changed" } },
    };

    [Theory]
    [MemberData(nameof(EachFieldChange))]
    public void ChangingAnyField_BreaksEquality(string field, Func<Token, Token> change)
    {
        var original = Sample();
        var changed = change(original);

        Assert.NotEqual(original, changed);
        Assert.True(original != changed, $"{field}: the inequality operator must observe the change.");
        // The original is untouched: a copy never mutates its source.
        Assert.Equal(Sample(), original);
    }

    [Theory]
    [MemberData(nameof(EachFieldChange))]
    public void Copy_PreservesEveryOtherField(string field, Func<Token, Token> change)
    {
        var original = Sample();
        var copy = change(original);

        // The changed field really changed; the six others are carried across.
        var property = typeof(Token).GetProperty(field)!;
        Assert.NotEqual(property.GetValue(original), property.GetValue(copy));
        Assert.NotEqual(original, copy);
        Assert.NotSame(original, copy);
        Assert.Equal(Sample(), original);
        if (field != "Kind") Assert.Equal(original.Kind, copy.Kind);
        if (field != "Position") Assert.Equal(original.Position, copy.Position);
        if (field != "Length") Assert.Equal(original.Length, copy.Length);
        if (field != "Line") Assert.Equal(original.Line, copy.Line);
        if (field != "Column") Assert.Equal(original.Column, copy.Column);
        if (field != "NumValue") Assert.Equal(original.NumValue, copy.NumValue);
        if (field != "StringValue") Assert.Equal(original.StringValue, copy.StringValue);

        // An unchanged copy is equal and a distinct instance.
        var same = original with { };
        Assert.NotSame(original, same);
        Assert.Equal(original, same);
        Assert.Equal(original.GetHashCode(), same.GetHashCode());
    }

    [Fact]
    public void Copy_CarriesAPayloadThroughAnUnrelatedChange()
    {
        // The doctored-token harness relies on this: moving a token keeps its text and value.
        var identifier = Token.CreateIdentifier("value", 4, 5, 1, 5);
        var moved = identifier with { Position = 40 };
        Assert.Equal("value", moved.StringValue);
        Assert.Equal(TokenKind.Identifier, moved.Kind);

        var number = Token.CreateNumber(Decimal128.Parse("2.5", System.Globalization.CultureInfo.InvariantCulture), 0, 3, 1, 1);
        var relined = number with { Line = 9 };
        Assert.Equal(number.NumValue, relined.NumValue);
        Assert.Equal(TokenKind.Number, relined.Kind);
    }

    [Fact]
    public void Factories_PairEachKindWithItsPayload()
    {
        var number = Token.CreateNumber(42, 1, 2, 3, 4);
        Assert.Equal(new Token(TokenKind.Number, 1, 2, 3, 4, 42), number);
        Assert.Null(number.StringValue);

        var identifier = Token.CreateIdentifier("abc", 1, 3, 3, 4);
        Assert.Equal(new Token(TokenKind.Identifier, 1, 3, 3, 4, stringValue: "abc"), identifier);
        Assert.Equal(default, identifier.NumValue);

        var literal = Token.CreateStringLiteral("text", 1, 6, 3, 4);
        Assert.Equal(new Token(TokenKind.StringLiteral, 1, 6, 3, 4, stringValue: "text"), literal);
        Assert.Equal(default, literal.NumValue);

        var comment = Token.CreateComment(" note", 1, 6, 3, 4);
        Assert.Equal(new Token(TokenKind.Comment, 1, 6, 3, 4, stringValue: " note"), comment);
        Assert.Equal(default, comment.NumValue);

        var plus = Token.Create(TokenKind.Plus, 1, 1, 3, 4);
        Assert.Equal(new Token(TokenKind.Plus, 1, 1, 3, 4), plus);
        Assert.Null(plus.StringValue);
        Assert.Equal(default, plus.NumValue);

        var eof = Token.EndOfFile(9, 3, 4);
        Assert.Equal(new Token(TokenKind.EndOfFile, 9, 0, 3, 4), eof);
        Assert.Equal(0, eof.Length);

        // The parser's Expect recovery mints a ZERO-length Bad token; the lexer's Bad
        // tokens have the length of the unexpected code unit(s). Both are the one factory.
        Assert.Equal(new Token(TokenKind.Bad, 5, 0, 1, 6), Token.Bad(5, 0, 1, 6));
        Assert.Equal(new Token(TokenKind.Bad, 5, 2, 1, 6), Token.Bad(5, 2, 1, 6));
    }

    // The diagnostic is positioned at the current token's own extent: the four-column name,
    // or an EMPTY span at end of input — no fabricated one-column width past the text.
    [Theory]
    [InlineData("name", "a name", 5)]
    [InlineData("", "end of input", 1)]
    public void ParserExpect_UsesAnInternalZeroLengthBadMarkerWithoutConsumingInput(string source, string found, int diagnosticEndColumn)
    {
        const System.Reflection.BindingFlags flags = System.Reflection.BindingFlags.NonPublic | System.Reflection.BindingFlags.Instance;
        var tokens = Lexer.Tokenize(source).Tokens;
        var diagnostics = new List<Diagnostic>();
        var parser = (Parser)Assert.Single(typeof(Parser).GetConstructors(flags)).Invoke([tokens, diagnostics, null]);
        var marker = Assert.IsType<Token>(typeof(Parser).GetMethod("Expect", flags)!.Invoke(parser, [TokenKind.RParen]));
        Assert.Equal(Token.Bad(0, 0, 1, 1), marker);
        Assert.Same(tokens[0], typeof(Parser).GetProperty("Current", flags)!.GetValue(parser));
        var diagnostic = Assert.Single(diagnostics);
        Assert.Equal(DiagnosticCode.UnexpectedToken, diagnostic.Code);
        Assert.Equal(DiagnosticSeverity.Error, diagnostic.Severity);
        Assert.Equal($"Expected ')' but found {found}.", diagnostic.Message);
        Assert.Equal(new SourceSpan(1, 1, 1, diagnosticEndColumn), diagnostic.Span);
        Assert.Equal(new SourceSpan(1, 1, 1, 1), marker.Span);   // the zero-length marker is an empty span at its position
        Assert.Equal(source.Length == 0, Assert.NotNull(diagnostic.Span).IsEmpty);
    }

    // ── Production valid-state matrix ────────────────────────────────────────

    /// <summary>
    /// One source that produces every <see cref="TokenKind"/> (including a lexer Bad
    /// token for a supplementary-plane character and one for a BMP character), so the
    /// payload rules can be checked kind by kind on real lexer output.
    /// </summary>
    private const string EveryKindSource =
        "# heading\n"
        + "A(x) = x ^ 2 + 1 - 3 * 4 / 5\n"
        + "B = 'text' <= 2 and not (3 >= 4) or 5 != 6 xor 7 == 8 < 9 > 0\n"
        + "public C = [10 div 3, 10 mod 3]; {open Math}, B:1, A~.t\n"
        + "@ \U0001F600 D = 1.5e3\n";

    [Fact]
    public void EveryTokenKind_IsProducedByTheMatrixSource()
    {
        var (tokens, _) = Lexer.Tokenize(EveryKindSource);
        var produced = tokens.Select(t => t.Kind).ToHashSet();
        var missing = Enum.GetValues<TokenKind>().Where(kind => !produced.Contains(kind)).ToList();
        Assert.True(missing.Count == 0, "The matrix source must produce every kind; missing: " + string.Join(", ", missing));
    }

    [Fact]
    public void ProductionTokens_CarryExactlyThePayloadTheirKindOwns()
    {
        var (tokens, _) = Lexer.Tokenize(EveryKindSource);

        foreach (var token in tokens)
        {
            switch (token.Kind)
            {
                case TokenKind.Number:
                    Assert.Null(token.StringValue);
                    break;
                case TokenKind.Identifier:
                case TokenKind.StringLiteral:
                case TokenKind.Comment:
                    Assert.NotNull(token.StringValue);
                    Assert.Equal(default, token.NumValue);
                    break;
                default:
                    Assert.Null(token.StringValue);
                    Assert.Equal(default, token.NumValue);
                    break;
            }
        }

        // The text payloads are the documented slices of the source.
        Assert.All(tokens.Where(t => t.Kind == TokenKind.Identifier), t =>
            Assert.Equal(EveryKindSource.Substring(t.Position, t.Length), t.StringValue));
        Assert.All(tokens.Where(t => t.Kind == TokenKind.StringLiteral), t =>
            Assert.Equal(EveryKindSource.Substring(t.Position + 1, t.Length - 2), t.StringValue));
        Assert.All(tokens.Where(t => t.Kind == TokenKind.Comment), t =>
            Assert.Equal(EveryKindSource.Substring(t.Position + 1, t.Length - 1), t.StringValue));

        // Keywords carry no text: their spelling is the source slice.
        var keywords = tokens.Where(t => t.Kind is >= TokenKind.KeywordDiv and <= TokenKind.KeywordOpen).ToList();
        Assert.Equal(Lexer.KeywordNames.Count, keywords.Select(t => t.Kind).Distinct().Count());
        Assert.All(keywords, t => Assert.Contains(EveryKindSource.Substring(t.Position, t.Length), Lexer.KeywordNames));
    }

    [Fact]
    public void ProductionTokens_KeepTheCoordinateRules()
    {
        var (tokens, diagnostics) = Lexer.Tokenize(EveryKindSource);

        // Every token is inside the source and at least one code unit wide, except the
        // one end-of-file token, which is last, empty, and at the source length.
        var eof = tokens[^1];
        Assert.Equal(TokenKind.EndOfFile, eof.Kind);
        Assert.Equal(0, eof.Length);
        Assert.Equal(EveryKindSource.Length, eof.Position);
        Assert.Single(tokens, t => t.Kind == TokenKind.EndOfFile);

        foreach (var token in tokens.SkipLast(1))
        {
            Assert.True(token.Length >= 1, $"{token.Kind} at {token.Position} is empty.");
            Assert.InRange(token.Position, 0, EveryKindSource.Length - token.Length);
            Assert.True(token.Line >= 1 && token.Column >= 1, $"{token.Kind} at {token.Position} has a non-positive line/column.");
            Assert.DoesNotContain('\n', EveryKindSource.AsSpan(token.Position, token.Length).ToString());
        }

        // Tokens advance strictly, and the recorded line/column agree with the offset.
        for (var i = 1; i < tokens.Count; i++)
            Assert.True(tokens[i].Position >= tokens[i - 1].Position + tokens[i - 1].Length, $"token {i} overlaps its predecessor");
        foreach (var token in tokens)
        {
            var before = EveryKindSource.AsSpan(0, token.Position);
            var lastBreak = before.LastIndexOf('\n');
            Assert.Equal(1 + before.Count('\n'), token.Line);
            Assert.Equal(token.Position - lastBreak, token.Column);
        }

        // The lexer's Bad tokens are one code unit wide, or two for a surrogate pair,
        // each with its own diagnostic; the zero-length Bad token is the parser's alone.
        var bad = tokens.Where(t => t.Kind == TokenKind.Bad).ToList();
        Assert.Equal(2, bad.Count);
        Assert.Equal([1, 2], bad.Select(t => t.Length));
        Assert.Equal(bad.Count, diagnostics.Count(d => d.Code == DiagnosticCode.UnexpectedCharacter));
    }
}
