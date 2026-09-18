using System.Reflection;
using System.Runtime.CompilerServices;

namespace KatLang.Tests;

/// <summary>
/// The parser's two balanced state protocols — the cumulative recursion budget
/// (<c>Parser.MaxNestingDepth</c>: one base unit per expression, unary, and clause-head
/// pattern level, plus a calibrated surcharge per heavy delimited production) and the owed
/// closing delimiters (<c>Parser.IsOwedCloser</c>) — are entered and released through
/// scoped disposables (<c>Parser.EnterNestingLevel</c> / <c>Parser.EnterDelimitedProduction</c>)
/// instead of hand-balanced <c>try</c>/<c>finally</c> pairs, so no production can release a
/// different amount than it charged or forget a release on a recovery path.
///
/// <para>The calibrated charge boundaries themselves are pinned by
/// <c>ParserNestingDepthTests</c>. These tests pin the RELEASE on the paths a hand-balanced
/// protocol gets wrong: a production that exits through error recovery must leave the
/// budget and the owed-closer counters exactly as it found them, so a later row parses
/// against the very same budget boundary as in a control document without the recovered
/// row, and a later stray closer is still a root stray rather than an owed one.</para>
/// </summary>
public class ParserScopedStateTests
{
    // Direct protocol probes are necessary for exceptions that abort the whole parse:
    // the public parse result deliberately discards the parser instance on those paths.
    private static Parser NewParser()
        => (Parser)typeof(Parser).GetConstructors(BindingFlags.NonPublic | BindingFlags.Instance).Single()
            .Invoke([Lexer.Tokenize("1").Tokens, new List<Diagnostic>(), null]);

    private static IDisposable Enter(Parser parser, bool delimited)
        => (IDisposable)typeof(Parser).GetMethod(
            delimited ? "EnterDelimitedProduction" : "EnterNestingLevel", BindingFlags.NonPublic | BindingFlags.Instance)!
            .Invoke(parser, delimited ? [TokenKind.RParen, 1] : null)!;

    private static (int Depth, int Parens, int Brackets, int Braces) State(Parser parser)
    {
        int Field(string name) => (int)typeof(Parser).GetField(name, BindingFlags.NonPublic | BindingFlags.Instance)!.GetValue(parser)!;
        return (Field("_nestingDepth"), Field("_openParens"), Field("_openBrackets"), Field("_openBraces"));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void Scopes_RejectCopiedAndOutOfOrderDisposal_WithoutRestoringAnotherScope(bool delimited)
    {
        var parser = NewParser();
        var outer = Enter(parser, delimited);
        var copied = (IDisposable)RuntimeHelpers.GetObjectValue(outer);
        var outerState = State(parser);
        var inner = Enter(parser, !delimited);
        var innerState = State(parser);
        Assert.Throws<InvalidOperationException>(() => copied.Dispose());
        Assert.Equal(innerState, State(parser));
        inner.Dispose();
        Assert.Equal(outerState, State(parser));
        outer.Dispose();
        using (Enter(parser, delimited))
        {
            Assert.Throws<InvalidOperationException>(() => copied.Dispose());
            Assert.Equal(outerState, State(parser));
        }
        ((IDisposable)Activator.CreateInstance(outer.GetType())!).Dispose();
        Assert.Equal((0, 0, 0, 0), State(parser));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void RejectedEntry_AndExceptionalUnwind_RestoreTheExactParserState(bool delimited)
    {
        var parser = NewParser();
        using (Enter(parser, !delimited))
        {
            var outerState = State(parser);
            Assert.Throws<OperationCanceledException>((Action)(() =>
            {
                using var inner = Enter(parser, delimited);
                throw new OperationCanceledException();
            }));
            Assert.Equal(outerState, State(parser));
        }

        var depth = typeof(Parser).GetField("_nestingDepth", BindingFlags.NonPublic | BindingFlags.Instance)!;
        depth.SetValue(parser, Parser.MaxNestingDepth);
        var before = State(parser);
        var failure = Assert.Throws<TargetInvocationException>(() => Enter(parser, delimited));
        Assert.Equal("NestingLimitExceededException", failure.InnerException!.GetType().Name);
        Assert.Equal(before, State(parser));
    }

    private static string Rep(string s, int n) => string.Concat(Enumerable.Repeat(s, n));

    private static bool HasNestingDiagnostic(SyntaxParseResult result)
        => result.Diagnostics.Any(d => d.Code == DiagnosticCode.NestingTooDeep);

    private static string Describe(Diagnostic diagnostic)
        => $"[{diagnostic.Code}] {Assert.NotNull(diagnostic.Span).Start.Line}:{Assert.NotNull(diagnostic.Span).Start.Column} {diagnostic.Message}";

    /// <summary>
    /// The deepest level count in <c>[1, 400]</c> at which <paramref name="sourceAt"/> parses
    /// without the budget diagnostic (the budget is monotonic in the level count).
    /// </summary>
    private static int DeepestAdmitted(Func<int, string> sourceAt)
    {
        int low = 1, high = 400;
        Assert.False(HasNestingDiagnostic(Parser.ParseSyntax(sourceAt(low))));
        Assert.True(HasNestingDiagnostic(Parser.ParseSyntax(sourceAt(high))));
        while (high - low > 1)
        {
            var middle = (low + high) / 2;
            if (HasNestingDiagnostic(Parser.ParseSyntax(sourceAt(middle))))
                high = middle;
            else
                low = middle;
        }

        return low;
    }

    /// <summary>
    /// One recovered instance of each heavy delimited production (the five
    /// <c>EnterDelimitedProduction</c> sites: group, call argument list, trailing-brace call
    /// argument, brace block, list literal), each exited through the owed-closer recovery.
    /// </summary>
    public static TheoryData<string> RecoveredProductions => new()
    {
        "A = (1 + )",
        "F(a) = a\nA = F(1, )",
        "F(a) = a\nA = F{1, }",
        "A = {1, }",
        "A = [1, ]",
    };

    /// <summary>
    /// The three base-unit chokepoints (expression, unary, clause-head pattern), each exited
    /// through recovery on a row that CLOSES on its line (a row whose recovered construct
    /// stays open swallows the next row and is a different, structural charge).
    /// </summary>
    public static TheoryData<string> RecoveredChokepoints => new()
    {
        "A = 1 + )",
        "A = - )",
        "F((1, ~x)) = 1",
        "F((1, -)) = 1",
    };

    [Theory]
    [MemberData(nameof(RecoveredProductions))]
    [MemberData(nameof(RecoveredChokepoints))]
    public void RecoveredRow_ReleasesEveryBudgetCharge_SoTheNextRowMeetsTheControlBoundary(string recoveredRow)
    {
        // The next row is a nested-group chain and a prefix chain: with any unit leaked by
        // the recovered row, the deepest admitted chain would shrink by at least one level.
        string GroupRow(int levels) => "B = " + Rep("(", levels) + "1" + Rep(")", levels) + "\nB";
        string PrefixRow(int levels) => "B = " + Rep("-", levels) + "1\nB";

        Assert.Equal(DeepestAdmitted(GroupRow), DeepestAdmitted(levels => recoveredRow + "\n" + GroupRow(levels)));
        Assert.Equal(DeepestAdmitted(PrefixRow), DeepestAdmitted(levels => recoveredRow + "\n" + PrefixRow(levels)));

        var recovered = Parser.ParseSyntax(recoveredRow + "\n" + GroupRow(DeepestAdmitted(GroupRow)));
        Assert.Contains(recovered.Diagnostics, d => d.Code != DiagnosticCode.NestingTooDeep);
        Assert.Contains(Assert.IsType<Algorithm.User>(recovered.Root).Properties, p => p.Name == "B");
    }

    [Theory]
    [MemberData(nameof(RecoveredProductions))]
    public void RecoveredProduction_ReleasesItsOwedCloser_SoALaterStrayCloserIsStillARootStray(string recoveredRow)
    {
        // With the recovered row's closer still counted as owed, the root's stray-closer
        // recovery would treat these closers as owed by an enclosing construct instead of
        // reporting them as top-level strays. The control document replaces each stray by a
        // space, so the recovered parse must reproduce its declarations and its other
        // diagnostics exactly.
        var recovered = Parser.ParseSyntax(recoveredRow + "\n)\n}\nB = 2\nB");
        var control = Parser.ParseSyntax(recoveredRow + "\n \n \nB = 2\nB");

        var strays = recovered.Diagnostics.Where(d => d.Message.Contains("at the top level", StringComparison.Ordinal)).ToList();
        Assert.Equal(2, strays.Count);
        var strayParenLine = recoveredRow.Count(c => c == '\n') + 2;
        Assert.Contains(strays, d => d.Message.StartsWith("Unexpected ')' at the top level", StringComparison.Ordinal) && Assert.NotNull(d.Span).Start.Line == strayParenLine);
        Assert.Contains(strays, d => d.Message.StartsWith("Unexpected '}' at the top level", StringComparison.Ordinal) && Assert.NotNull(d.Span).Start.Line == strayParenLine + 1);
        Assert.Equal(
            control.Diagnostics.Select(Describe),
            recovered.Diagnostics.Except(strays).Select(Describe));
        Assert.Equal(
            Assert.IsType<Algorithm.User>(control.Root).Properties.Select(p => p.Name),
            Assert.IsType<Algorithm.User>(recovered.Root).Properties.Select(p => p.Name));
    }

    [Fact]
    public void BudgetRejection_IsReportedOnce_AndTheParseEndsWithThePlaceholderRoot()
    {
        // The refused enter withdraws its own charge before the budget diagnostic aborts the
        // parse, and every admitted level releases on the unwind: exactly one structured
        // diagnostic, and the placeholder root — never a partially built tree.
        var result = Parser.ParseSyntax("A = 1\n" + Rep("(", 200) + "1" + Rep(")", 200) + "\nA");

        Assert.Single(result.Diagnostics, d => d.Code == DiagnosticCode.NestingTooDeep);
        var root = Assert.IsType<Algorithm.User>(result.Root);
        Assert.Empty(root.Properties);
        Assert.Empty(root.Output);
    }
}
