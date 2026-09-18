using System.Reflection;

namespace KatLang.Formatting.PublicApi.Tests;

/// <summary>
/// Pins the public location model (public API cleanup Task 3b) exactly as a NuGet consumer
/// meets it, with the pinned SDK's own compiler: <see cref="SourcePosition"/> and
/// <see cref="SourceSpan"/> are constructible, readable value types; <see cref="Diagnostic.Span"/>
/// and <see cref="KatLangError.Span"/> are nullable structured spans; <see cref="Token.Span"/> is a
/// derived span; and the retired flattened coordinate channels are gone, so old code fails to
/// compile with the precise error each removal produces rather than silently reading a
/// differently-based coordinate.
/// </summary>
public class SourceLocationPublicSurfaceTests
{
    private const string ProbePreamble = """
        using System.Collections.Generic;
        using KatLang;
        using KatLang.Semantics;
        namespace Consumer;
        public static class Fixtures
        {
            public static Token Token => Lexer.Tokenize("x = 1").Tokens[0];
            public static Diagnostic Diagnostic => Parser.Parse("(1").Diagnostics[0];
            public static KatLangError Error => ((RunResult.EvalFailure)KatLangEngine.Run("1 / 0")).Errors[0];
            public static SemanticModel Model => SemanticModelBuilder.Build(Parser.Parse("x = 1\nx"));
            public static SourceSpan Span => new SourceSpan(1, 1, 1, 2);
        }

        """;

    /// <summary>
    /// One retired spelling per row and the exact compiler error it must produce: the old
    /// flattened members no longer exist (CS1061 / CS0117), the four-int position queries
    /// are gone (CS1501), and neither location type accepts the old inclusive-end
    /// record members.
    /// </summary>
    private static readonly IReadOnlyList<(string Name, string Statement, string Code, string MemberNamed)> RetiredSpellings =
    [
        ("ErrorStartLine", "_ = Fixtures.Error.StartLine;", "CS1061", "'KatLangError' does not contain a definition for 'StartLine'"),
        ("ErrorStartColumn", "_ = Fixtures.Error.StartColumn;", "CS1061", "'KatLangError' does not contain a definition for 'StartColumn'"),
        ("ErrorEndLine", "_ = Fixtures.Error.EndLine;", "CS1061", "'KatLangError' does not contain a definition for 'EndLine'"),
        ("ErrorEndColumn", "_ = Fixtures.Error.EndColumn;", "CS1061", "'KatLangError' does not contain a definition for 'EndColumn'"),
        ("SpanStartLineNumber", "_ = Fixtures.Span.StartLineNumber;", "CS1061", "'SourceSpan' does not contain a definition for 'StartLineNumber'"),
        ("SpanStartColumn", "_ = Fixtures.Span.StartColumn;", "CS1061", "'SourceSpan' does not contain a definition for 'StartColumn'"),
        ("SpanEndLineNumber", "_ = Fixtures.Span.EndLineNumber;", "CS1061", "'SourceSpan' does not contain a definition for 'EndLineNumber'"),
        ("SpanEndColumn", "_ = Fixtures.Span.EndColumn;", "CS1061", "'SourceSpan' does not contain a definition for 'EndColumn'"),
        ("DiagnosticSpanIsNotPlain", "SourceSpan plain = Fixtures.Diagnostic.Span;", "CS0266", "Cannot implicitly convert type 'KatLang.SourceSpan?' to 'KatLang.SourceSpan'"),
        ("ErrorSpanIsNotPlain", "SourceSpan plain = Fixtures.Error.Span;", "CS0266", "Cannot implicitly convert type 'KatLang.SourceSpan?' to 'KatLang.SourceSpan'"),
        ("FindResolutionAtInts", "_ = Fixtures.Model.FindResolutionAt(2, 1);", "CS1501", "No overload for method 'FindResolutionAt' takes 2 arguments"),
        ("FindPropertyAtInts", "_ = Fixtures.Model.FindPropertyAt(2, 1);", "CS1501", "No overload for method 'FindPropertyAt' takes 2 arguments"),
        ("FindScopeAtInts", "_ = Fixtures.Model.FindScopeAt(2, 1);", "CS1501", "No overload for method 'FindScopeAt' takes 2 arguments"),
        ("VisibleSymbolsAtInts", "_ = Fixtures.Model.GetVisibleSymbolsAt(2, 1);", "CS1501", "No overload for method 'GetVisibleSymbolsAt' takes 2 arguments"),
        ("TokenSpanIsReadOnly", "_ = Fixtures.Token with { Span = Fixtures.Span };", "CS0200", "'Token.Span' cannot be assigned to"),
    ];

    [Fact]
    public void AConsumer_CannotUseTheRetiredFlattenedCoordinateSpellings()
    {
        var source = new System.Text.StringBuilder(ProbePreamble);
        source.Append("public static class Retired\n{\n");
        foreach (var (name, statement, _, _) in RetiredSpellings)
            source.Append("    public static void ").Append(name).Append("() { ").Append(statement).Append(" }\n");
        source.Append("}\n");

        var compilation = ConsumerCompiler.Compile(source.ToString(), "location-retired");
        Assert.NotEqual(0, compilation.ExitCode);

        var lines = source.ToString().Split('\n');
        foreach (var (name, statement, code, memberNamed) in RetiredSpellings)
        {
            var line = Array.FindIndex(lines, l => l.Contains(statement, StringComparison.Ordinal)) + 1;
            Assert.True(line > 0, $"probe {name} not found in the generated source");
            var onLine = compilation.Diagnostics.Where(d => d.Line == line).ToList();
            var match = Assert.Single(onLine);
            Assert.True(
                match.Code == code && match.Message.Contains(memberNamed, StringComparison.Ordinal),
                $"{name}: expected {code} naming {memberNamed} for `{statement}`; got {match.Code}: {match.Message}"
                + Environment.NewLine + compilation.Output);
        }

        // Only the refusals above: nothing else in the probe fails to compile.
        Assert.Equal(RetiredSpellings.Count, compilation.Diagnostics.Count);
    }

    [Fact]
    public void AConsumer_ConstructsAndReadsTheLocationTypes()
    {
        // The positive control: everything the model is FOR compiles for a consumer.
        const string source = ProbePreamble + """
            public static class Valid
            {
                // Real coordinates are constructible; both spellings build the same half-open span.
                public static SourceSpan Build()
                {
                    var start = new SourcePosition(4, 15);
                    var end = new SourcePosition(4, 21);
                    var fromPositions = new SourceSpan(start, end);
                    var fromInts = new SourceSpan(4, 15, 4, 21);
                    return fromPositions == fromInts ? fromPositions : throw new System.InvalidOperationException();
                }

                // Coordinates read back through the structured members; value equality and hashing work.
                public static string Describe(SourceSpan span)
                {
                    var (start, end) = span;
                    var (line, column) = start;
                    var set = new HashSet<SourceSpan> { span };
                    return $"{line}:{column}-{end.Line}:{end.Column} {span.IsEmpty} {span.Contains(start)} {span.Union(span)} {set.Contains(span)} {start < end} {start.CompareTo(end)}";
                }

                // Diagnostics and public errors may be unpositioned: the span is nullable, and null means absent.
                public static string Where(Diagnostic diagnostic, KatLangError error)
                {
                    var diagnosticText = diagnostic.Span is { } d ? d.ToString() : "unpositioned";
                    var errorText = error.Span is { } e ? $"{e.Start.Line}:{e.Start.Column}" : "unpositioned";
                    return diagnosticText + " " + errorText;
                }

                // A token's span is derived from its stored offset model; the offsets stay separate.
                public static (int Position, int Length, SourceSpan Span) Extent(Token token)
                    => (token.Position, token.Length, token.Span);

                // The editor queries take a position.
                public static int Query(SemanticModel model)
                {
                    var cursor = new SourcePosition(2, 1);
                    var resolution = model.FindResolutionAt(cursor);
                    var property = model.FindPropertyAt(cursor);
                    var scope = model.FindScopeAt(cursor);
                    var visible = model.GetVisibleSymbolsAt(cursor);
                    return (resolution is null ? 0 : 1) + (property is null ? 0 : 1) + scope.Symbols.Count + visible.Count;
                }

                // Nullable spans compose with ordinary null handling.
                public static SourceSpan? Prefer(SourceSpan? own, SourceSpan? fallback) => own ?? fallback;
            }

            """;

        var compilation = ConsumerCompiler.Compile(source, "location-reads");

        Assert.True(
            compilation.ExitCode == 0 && compilation.Diagnostics.Count == 0,
            "Every legitimate location read must compile for a consumer." + Environment.NewLine + compilation.Output);
    }

    [Fact]
    public void TheLocationTypes_ArePublicReadonlyRecordStructs_WithValidatedConstruction()
    {
        foreach (var type in new[] { typeof(SourcePosition), typeof(SourceSpan) })
        {
            Assert.True(type.IsPublic);
            Assert.True(type.IsValueType);
            Assert.True(type.IsDefined(typeof(System.Runtime.CompilerServices.IsReadOnlyAttribute), inherit: false), $"{type.Name} must be readonly");
            Assert.NotNull(type.GetMethod("PrintMembers", BindingFlags.NonPublic | BindingFlags.Instance)); // a record struct
            Assert.All(type.GetProperties(BindingFlags.Public | BindingFlags.Instance), p => Assert.Null(p.SetMethod));
            Assert.Empty(type.GetFields(BindingFlags.Public | BindingFlags.Instance));
        }

        Assert.Equal(
            ["Column", "Line"],
            typeof(SourcePosition).GetProperties(BindingFlags.Public | BindingFlags.Instance).Select(p => p.Name).Order(StringComparer.Ordinal));
        Assert.Equal(
            ["End", "IsEmpty", "Start"],
            typeof(SourceSpan).GetProperties(BindingFlags.Public | BindingFlags.Instance).Select(p => p.Name).Order(StringComparer.Ordinal));
        Assert.Contains(typeof(IComparable<SourcePosition>), typeof(SourcePosition).GetInterfaces());

        // Validation is a construction-time invariant of the public constructors.
        Assert.Throws<ArgumentOutOfRangeException>(() => new SourcePosition(0, 1));
        Assert.Throws<ArgumentOutOfRangeException>(() => new SourceSpan(1, 2, 1, 1));
        Assert.Throws<ArgumentOutOfRangeException>(() => new SourceSpan(default, new SourcePosition(1, 1)));

        // The public location-bearing properties are the nullable structured span.
        Assert.Equal(typeof(SourceSpan?), typeof(Diagnostic).GetProperty(nameof(Diagnostic.Span))!.PropertyType);
        Assert.Equal(typeof(SourceSpan?), typeof(KatLangError).GetProperty(nameof(KatLangError.Span))!.PropertyType);
        Assert.Equal(typeof(SourceSpan?), typeof(EvalError).GetProperty(nameof(EvalError.Span))!.PropertyType);
        Assert.Equal(typeof(SourceSpan), typeof(Token).GetProperty(nameof(Token.Span))!.PropertyType);
        Assert.Null(typeof(KatLangError).GetProperty("StartLine"));
        Assert.Null(typeof(KatLangError).GetProperty("EndColumn"));
    }
}
