using System.Reflection;
using System.Runtime.CompilerServices;
using System.Text;

namespace KatLang.Formatting.PublicApi.Tests;

/// <summary>
/// Pins the construction contract of the public <see cref="Token"/> type against the
/// compiled assembly, exactly as a NuGet consumer meets it (this project is deliberately
/// not a friend assembly): KatLang creates tokens, consumers inspect them. A consumer
/// obtains tokens from <see cref="Lexer.Tokenize(string)"/> and reads every property, but
/// cannot construct a token, call a factory, set or <c>with</c>-mutate a property, or
/// deconstruct one positionally — each refusal is a COMPILE error witnessed by the pinned
/// SDK's own compiler, with the precise error the design names, and the same compiler
/// must accept every legitimate read so the negative verdicts cannot be vacuous.
/// </summary>
public class TokenPublicSurfaceTests
{
    /// <summary>
    /// One invalid consumer statement per row and the exact compiler errors it must
    /// produce. A consumer compiles against the assembly's PUBLIC surface, so the
    /// internal constructor and factories are not merely inaccessible but absent from
    /// its view ("does not contain a constructor" / "does not contain a definition"),
    /// and a property whose init accessor is internal is read-only to it; an object
    /// initializer and a deconstruction are each refused with two errors on their line.
    /// Every row names the member it targets, so a row cannot pass on an unrelated refusal.
    /// </summary>
    private static readonly IReadOnlyList<(string Name, string Statement, IReadOnlyList<(string Code, string MemberNamed)> Expected)> InvalidStates =
    [
        // Direct construction: the one constructor is internal, and so is the object-initializer route.
        ("Constructor", "_ = new Token(TokenKind.Number, 0, 1, 1, 1);", [("CS1729", "'Token' does not contain a constructor that takes 5 arguments")]),
        ("ConstructorWithPayload", "_ = new Token(TokenKind.Number, 0, 1, 1, 1, 42, null);", [("CS1729", "'Token' does not contain a constructor that takes 7 arguments")]),
        ("ObjectInitializer", "_ = new Token { Kind = TokenKind.Number };", [("CS1729", "'Token' does not contain a constructor that takes 0 arguments"), ("CS0200", "'Token.Kind' cannot be assigned to")]),
        ("CopyConstructor", "_ = new Token(Existing);", [("CS1729", "'Token' does not contain a constructor that takes 1 arguments")]),
        ("ConstructorWithNumber", "_ = new Token(TokenKind.Number, 0, 1, 1, 1, 42);", [("CS1729", "'Token' does not contain a constructor that takes 6 arguments")]),
        ("InitializerPosition", "_ = new Token { Position = 99 };", [("CS1729", "'Token' does not contain a constructor that takes 0 arguments"), ("CS0200", "'Token.Position' cannot be assigned to")]),
        ("InitializerLength", "_ = new Token { Length = 0 };", [("CS1729", "'Token' does not contain a constructor that takes 0 arguments"), ("CS0200", "'Token.Length' cannot be assigned to")]),
        ("InitializerLine", "_ = new Token { Line = 9 };", [("CS1729", "'Token' does not contain a constructor that takes 0 arguments"), ("CS0200", "'Token.Line' cannot be assigned to")]),
        ("InitializerColumn", "_ = new Token { Column = 9 };", [("CS1729", "'Token' does not contain a constructor that takes 0 arguments"), ("CS0200", "'Token.Column' cannot be assigned to")]),
        ("InitializerNumValue", "_ = new Token { NumValue = 7 };", [("CS1729", "'Token' does not contain a constructor that takes 0 arguments"), ("CS0200", "'Token.NumValue' cannot be assigned to")]),
        ("InitializerStringValue", "_ = new Token { StringValue = \"forged\" };", [("CS1729", "'Token' does not contain a constructor that takes 0 arguments"), ("CS0200", "'Token.StringValue' cannot be assigned to")]),
        // Factories: all seven are internal.
        ("FactoryNumber", "_ = Token.CreateNumber(1, 0, 1, 1, 1);", [("CS0117", "'Token' does not contain a definition for 'CreateNumber'")]),
        ("FactoryIdentifier", "_ = Token.CreateIdentifier(\"a\", 0, 1, 1, 1);", [("CS0117", "'Token' does not contain a definition for 'CreateIdentifier'")]),
        ("FactoryStringLiteral", "_ = Token.CreateStringLiteral(\"a\", 0, 3, 1, 1);", [("CS0117", "'Token' does not contain a definition for 'CreateStringLiteral'")]),
        ("FactoryComment", "_ = Token.CreateComment(\"a\", 0, 2, 1, 1);", [("CS0117", "'Token' does not contain a definition for 'CreateComment'")]),
        ("FactoryCreate", "_ = Token.Create(TokenKind.Plus, 0, 1, 1, 1);", [("CS0117", "'Token' does not contain a definition for 'Create'")]),
        ("FactoryEndOfFile", "_ = Token.EndOfFile(0, 1, 1);", [("CS0117", "'Token' does not contain a definition for 'EndOfFile'")]),
        ("FactoryBad", "_ = Token.Bad(0, 1, 1, 1);", [("CS0117", "'Token' does not contain a definition for 'Bad'")]),
        // Mutation through `with`: every init accessor is internal, so the property is read-only to a consumer.
        ("WithKind", "_ = Existing with { Kind = TokenKind.Bad };", [("CS0200", "'Token.Kind' cannot be assigned to")]),
        ("WithPosition", "_ = Existing with { Position = 99 };", [("CS0200", "'Token.Position' cannot be assigned to")]),
        ("WithLength", "_ = Existing with { Length = 0 };", [("CS0200", "'Token.Length' cannot be assigned to")]),
        ("WithLine", "_ = Existing with { Line = 9 };", [("CS0200", "'Token.Line' cannot be assigned to")]),
        ("WithColumn", "_ = Existing with { Column = 9 };", [("CS0200", "'Token.Column' cannot be assigned to")]),
        ("WithNumValue", "_ = Existing with { NumValue = 7 };", [("CS0200", "'Token.NumValue' cannot be assigned to")]),
        ("WithStringValue", "_ = Existing with { StringValue = \"forged\" };", [("CS0200", "'Token.StringValue' cannot be assigned to")]),
        // Positional deconstruction: the record is non-positional and declares no Deconstruct.
        ("Deconstruct", "(TokenKind kind, int position, int length, int line, int column, Decimal128 numValue, string? stringValue) = Existing;", [("CS1061", "'Token' does not contain a definition for 'Deconstruct'"), ("CS8129", "No suitable 'Deconstruct' instance or extension method was found for type 'Token', with 7 out parameters")]),
        ("DeconstructCall", "Existing.Deconstruct(out TokenKind k, out int p, out int l, out int ln, out int c, out Decimal128 n, out string? s);", [("CS1061", "'Token' does not contain a definition for 'Deconstruct'")]),
    ];

    private const string ProbePreamble = """
        using System.Collections.Generic;
        using System.Numerics;
        using KatLang;
        namespace Consumer;
        public static class Fixtures
        {
            public static Token Existing => Lexer.Tokenize("x = 1").Tokens[0];
        }

        """;

    [Fact]
    public void AConsumer_CannotConstructMutateOrDeconstructAToken()
    {
        // Every invalid statement in one compilation, one method per row so each verdict
        // is attributable by line: the compiler must report exactly the named errors for
        // each row and nothing else.
        var source = new StringBuilder(ProbePreamble);
        source.Append("public static class Invalid\n{\n");
        foreach (var (name, statement, _) in InvalidStates)
        {
            source.Append($"    public static void {name}()\n    {{\n");
            source.Append("        var Existing = Fixtures.Existing;\n");
            source.Append("        _ = Existing;\n");
            source.Append("        ").Append(statement).Append('\n');
            source.Append("    }\n");
        }

        source.Append("}\n");

        var compilation = ConsumerCompiler.Compile(source.ToString(), "token-construction");

        Assert.NotEqual(0, compilation.ExitCode);
        var lines = source.ToString().Split('\n');
        var expectedTotal = 0;
        foreach (var (name, statement, expected) in InvalidStates)
        {
            var line = Array.FindIndex(lines, l => l.Contains(statement, StringComparison.Ordinal)) + 1;
            Assert.True(line > 0, $"probe {name} not found in the generated source");
            var onLine = compilation.Diagnostics.Where(d => d.Line == line).OrderBy(d => d.Code, StringComparer.Ordinal).ToList();
            var wanted = expected.OrderBy(e => e.Code, StringComparer.Ordinal).ToList();
            Assert.True(
                onLine.Count == wanted.Count
                    && onLine.Zip(wanted).All(pair =>
                        pair.First.Code == pair.Second.Code
                        && pair.First.Message.Contains(pair.Second.MemberNamed, StringComparison.Ordinal)),
                $"{name}: expected [{string.Join(", ", wanted.Select(e => $"{e.Code} naming {e.MemberNamed}"))}] for `{statement}`; got ["
                + string.Join(", ", onLine.Select(d => $"{d.Code}: {d.Message}")) + "]"
                + Environment.NewLine + compilation.Output);
            expectedTotal += wanted.Count;
        }

        // Only the refusals above: nothing else in the probe fails to compile.
        Assert.Equal(expectedTotal, compilation.Diagnostics.Count);
    }

    [Fact]
    public void AConsumer_ObtainsTokensFromTheLexer_AndReadsEveryProperty()
    {
        // The positive control: everything the type is FOR compiles for a consumer —
        // tokenizing, reading all seven properties by name, property patterns, value
        // equality, hashing, and exactly the reads the KatLangWeb colorizer performs.
        const string source = ProbePreamble + """
            public static class Valid
            {
                public static IReadOnlyList<Token> Tokens(string program) => Lexer.Tokenize(program).Tokens;

                public static string Describe(Token token)
                    => $"{token.Kind} @{token.Position}+{token.Length} ({token.Line}:{token.Column}) = {token.NumValue} / {token.StringValue}";

                public static int Sum(string program)
                {
                    var total = 0;
                    foreach (var token in Tokens(program))
                    {
                        total += token.Position + token.Length + token.Line + token.Column;
                        if (token is { Kind: TokenKind.Number, NumValue: var value } && value != default)
                            total += 1;
                        if (token is { Kind: TokenKind.Identifier, StringValue: { } name })
                            total += name.Length;
                    }
                    return total;
                }

                public static bool SameStream(string program)
                {
                    var first = Tokens(program);
                    var second = Tokens(program);
                    var seen = new HashSet<Token>(first);
                    for (var i = 0; i < first.Count; i++)
                    {
                        if (first[i] != second[i] || !first[i].Equals(second[i]) || !seen.Contains(second[i]))
                            return false;
                    }
                    return first.Count == second.Count;
                }

                // The reads KatLangWeb's colorizer performs (KatLangHelper.GetTokenSpans/GetTokenCssClass).
                public static string? CssClass(Token token, string program)
                {
                    if (token.Length <= 0)
                        return null;
                    var tokenKindName = token.Kind.ToString();
                    if (tokenKindName is "Comment")
                        return "katlang-token-comment";
                    if (tokenKindName is "Identifier" && token.StringValue is not null && token.StringValue.Length > 0)
                        return "katlang-token-identifier";
                    if (token.Position < 0 || token.Position + token.Length > program.Length)
                        return null;
                    var fragment = program.Substring(token.Position, token.Length);
                    return fragment is "{" or "}" ? "katlang-token-delimiter-curly" : null;
                }

                public static string Print(Token token) => token.ToString();
                public static Token Copy(Token token) => token with { };
                public static bool Equal(Token left, Token right) => left == right;
            }

            """;

        var compilation = ConsumerCompiler.Compile(source, "token-reads");

        Assert.True(
            compilation.ExitCode == 0 && compilation.Diagnostics.Count == 0,
            "Every legitimate token read must compile for a consumer." + Environment.NewLine + compilation.Output);
    }

    // ── Reflection half: the compiled shape ─────────────────────────────────

    private static readonly string[] TokenProperties = ["Kind", "Position", "Length", "Line", "Column", "NumValue", "StringValue"];

    [Fact]
    public void Token_IsAPublicSealedRecordClass_ReadableButNotConstructible()
    {
        var type = typeof(Token);
        Assert.True(type.IsPublic);
        Assert.True(type.IsSealed);
        Assert.True(type.IsClass);
        Assert.False(type.IsValueType);
        Assert.NotNull(type.GetMethod("<Clone>$", BindingFlags.Public | BindingFlags.Instance)); // a record

        // No public constructor; the one internal constructor takes the seven fields.
        Assert.Empty(type.GetConstructors(BindingFlags.Public | BindingFlags.Instance));
        var internalConstructor = Assert.Single(
            type.GetConstructors(BindingFlags.NonPublic | BindingFlags.Instance),
            c => c.IsAssembly);
        Assert.Equal(
            ["kind", "position", "length", "line", "column", "numValue", "stringValue"],
            internalConstructor.GetParameters().Select(p => p.Name));

        // A sealed record has just one other constructor: its PRIVATE copy constructor.
        var constructors = type.GetConstructors(BindingFlags.NonPublic | BindingFlags.Instance);
        Assert.Equal(2, constructors.Length);
        var copyConstructor = Assert.Single(constructors, c => c.IsPrivate);
        Assert.Equal([typeof(Token)], copyConstructor.GetParameters().Select(p => p.ParameterType));
        Assert.Empty(type.GetNestedTypes(BindingFlags.Public | BindingFlags.NonPublic));
        Assert.All(type.GetFields(BindingFlags.NonPublic | BindingFlags.Instance), f => Assert.True(f.IsPrivate));
        var clone = type.GetMethod("<Clone>$", BindingFlags.Public | BindingFlags.Instance)!;
        Assert.Equal(typeof(Token), clone.ReturnType);
        Assert.Empty(clone.GetParameters());
        Assert.False(clone.IsStatic);
        Assert.False(clone.IsVirtual); // sealed record: no consumer override/subclass hook

        // Every property has a public getter and an internal init-only setter.
        var properties = type.GetProperties(BindingFlags.Public | BindingFlags.Instance);
        Assert.Equal(TokenProperties.Order(StringComparer.Ordinal), properties.Select(p => p.Name).Order(StringComparer.Ordinal));
        foreach (var property in properties)
        {
            Assert.True(property.GetMethod is { IsPublic: true }, $"{property.Name} must be publicly readable.");
            var setter = property.SetMethod;
            Assert.True(setter is { IsAssembly: true }, $"{property.Name} must have an internal init accessor.");
            Assert.Contains(typeof(IsExternalInit), setter.ReturnParameter.GetRequiredCustomModifiers());
        }

        Assert.Empty(type.GetFields(BindingFlags.Public | BindingFlags.Instance | BindingFlags.Static));

        // No public factory, no Deconstruct at any accessibility; the seven factories are internal.
        var publicStatics = type.GetMethods(BindingFlags.Public | BindingFlags.Static | BindingFlags.DeclaredOnly).Select(m => m.Name).OrderBy(n => n, StringComparer.Ordinal);
        Assert.Equal(["op_Equality", "op_Inequality"], publicStatics);
        Assert.Empty(type.GetMember("Deconstruct", BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Instance | BindingFlags.Static));
        var factories = type.GetMethods(BindingFlags.NonPublic | BindingFlags.Static | BindingFlags.DeclaredOnly)
            .Where(m => m.IsAssembly && m.ReturnType == typeof(Token))
            .Select(m => m.Name)
            .OrderBy(n => n, StringComparer.Ordinal);
        Assert.Equal(["Bad", "Create", "CreateComment", "CreateIdentifier", "CreateNumber", "CreateStringLiteral", "EndOfFile"], factories);

        // The supported source of tokens stays public.
        var tokenize = typeof(Lexer).GetMethod("Tokenize", BindingFlags.Public | BindingFlags.Static, [typeof(string)]);
        Assert.NotNull(tokenize);
        Assert.Equal(typeof((IReadOnlyList<Token>, IReadOnlyList<Diagnostic>)), tokenize.ReturnType);
    }

    // ── Runtime half: the values a consumer sees ─────────────────────────────

    [Fact]
    public void ConsumerAssemblies_AreNotFriends()
    {
        var friends = typeof(Token).Assembly.GetCustomAttributes<InternalsVisibleToAttribute>()
            .Select(a => new AssemblyName(a.AssemblyName).Name).ToArray();
        Assert.DoesNotContain(typeof(TokenPublicSurfaceTests).Assembly.GetName().Name, friends);
        Assert.DoesNotContain("token-construction", friends);
        Assert.DoesNotContain("token-reads", friends);
    }

    [Fact]
    public void AConsumer_EmptyClonePreservesAllFields_AndRunsTheReadableContract()
    {
        // Executed in this genuinely non-friend assembly, not just compiled.
        const string source = "name = 2.5 # note\n'hello' + @";
        var tokens = Lexer.Tokenize(source).Tokens;
        var cloneMethod = typeof(Token).GetMethod("<Clone>$", BindingFlags.Public | BindingFlags.Instance)!;
        foreach (var original in tokens)
        {
            var copy = original with { };
            Assert.NotSame(original, copy);
            Assert.Equal(original, copy);
            Assert.True(original == copy);
            Assert.False(original != copy);
            Assert.True(original.Equals((object)copy));
            Assert.Equal(original.GetHashCode(), copy.GetHashCode());
            Assert.False(new HashSet<Token> { original }.Add(copy));
            Assert.Equal(original.ToString(), copy.ToString());
            Assert.Equal(
                (original.Kind, original.Position, original.Length, original.Line, original.Column, original.NumValue, original.StringValue),
                (copy.Kind, copy.Position, copy.Length, copy.Line, copy.Column, copy.NumValue, copy.StringValue));
            // Calling the generated public method through metadata exposes only the same copy.
            var reflectedCopy = Assert.IsType<Token>(cloneMethod.Invoke(original, null));
            Assert.NotSame(original, reflectedCopy);
            Assert.Equal(original, reflectedCopy);
        }
        Assert.True(tokens[0] is { Kind: TokenKind.Identifier, Position: 0, Length: 4, Line: 1, Column: 1, StringValue: "name" });
        Assert.True(tokens[2] is { Kind: TokenKind.Number, StringValue: null, NumValue: var value } && value != default);
    }

    [Fact]
    public void TokensFromSeparateTokenizations_AreEqualValues()
    {
        const string program = "# note\nTotal = sum((1, 2.5)) + 'text' # end\n";
        var first = Lexer.Tokenize(program).Tokens;
        var second = Lexer.Tokenize(program).Tokens;

        Assert.Equal(first.Count, second.Count);
        for (var i = 0; i < first.Count; i++)
        {
            Assert.NotSame(first[i], second[i]);
            Assert.Equal(first[i], second[i]);
            Assert.Equal(first[i].GetHashCode(), second[i].GetHashCode());
            Assert.True(first[i] == second[i]);
        }

        // Observable differences break equality: a different name, a different value,
        // a different kind at the same place, and the same token on a later line.
        Assert.NotEqual(Lexer.Tokenize("a").Tokens[0], Lexer.Tokenize("b").Tokens[0]);
        Assert.NotEqual(Lexer.Tokenize("1").Tokens[0], Lexer.Tokenize("2").Tokens[0]);
        Assert.NotEqual(Lexer.Tokenize("a").Tokens[0], Lexer.Tokenize("1").Tokens[0]);
        Assert.NotEqual(Lexer.Tokenize("a").Tokens[0], Lexer.Tokenize("\na").Tokens[0]);
        Assert.NotEqual(Lexer.Tokenize("a").Tokens[0], Lexer.Tokenize(" a").Tokens[0]);
    }

    [Fact]
    public void AConsumer_ReadsTheDocumentedPayloadAndCoordinates()
    {
        const string program = "value = 2.5 # note\n'text'";
        var tokens = Lexer.Tokenize(program).Tokens;

        Assert.Equal(
            [TokenKind.Identifier, TokenKind.Equals, TokenKind.Number, TokenKind.Comment, TokenKind.StringLiteral, TokenKind.EndOfFile],
            tokens.Select(t => t.Kind));

        var identifier = tokens[0];
        Assert.Equal(("value", 0, 5, 1, 1), (identifier.StringValue, identifier.Position, identifier.Length, identifier.Line, identifier.Column));
        Assert.Equal(default, identifier.NumValue);

        var equals = tokens[1];
        Assert.Null(equals.StringValue);
        Assert.Equal("=", program.Substring(equals.Position, equals.Length));

        var number = tokens[2];
        Assert.Equal(System.Numerics.Decimal128.Parse("2.5", System.Globalization.CultureInfo.InvariantCulture), number.NumValue);
        Assert.Null(number.StringValue);
        Assert.Equal("2.5", program.Substring(number.Position, number.Length));

        Assert.Equal(" note", tokens[3].StringValue);
        Assert.Equal(("text", 2, 1), (tokens[4].StringValue, tokens[4].Line, tokens[4].Column));

        var eof = tokens[5];
        Assert.Equal((program.Length, 0, 2, 7), (eof.Position, eof.Length, eof.Line, eof.Column));
        Assert.Null(eof.StringValue);
    }
}
