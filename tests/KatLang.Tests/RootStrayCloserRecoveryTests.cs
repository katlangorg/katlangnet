using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// Root-level stray-closer recovery (engine bug hunt K5-R3, September 2026).
///
/// <para>
/// An unmatched <c>)</c> or <c>}</c> at the ROOT used to end the parse: one
/// diagnostic, and every later declaration and output row vanished from the
/// syntax tree, the elaborated tree, and the SemanticModel. The root body now
/// reports the token in KatLang terms at its own span, consumes it, and keeps
/// parsing in the SAME root scope. The document stays invalid; the retained
/// tree serves diagnostics and editor analysis only, never evaluation. Since the
/// #9 parser-recovery audit an unmatched <c>]</c> recovers the same way (it used to
/// take the primary-expression fallback and invent a placeholder output row), and a
/// closer no open construct is waiting for closes the innermost open construct
/// instead of being consumed as junk (the delimiter-ownership law in Parser.cs).
/// </para>
///
/// <para>
/// Every source here is illegal by design (recovery is the subject), so the
/// permissive <see cref="SourceProvenance.ParseAllowingDiagnostics"/> path is
/// used deliberately. The oracle is the CONTROL document: the same text with
/// each stray closer replaced by one space, which preserves every line and
/// column, so the recovered parse must reproduce the control's tree, spans,
/// and non-stray diagnostics exactly. Templates mark each stray closer with
/// <c>¤</c> (one UTF-16 code unit), so one template yields both documents and
/// the expected diagnostic positions. That equivalence holds at ROW
/// BOUNDARIES; a closer in the middle of a row separates tokens that would
/// otherwise combine, and that shape is pinned on its own below.
/// </para>
/// </summary>
public class RootStrayCloserRecoveryTests
{
    private const char StrayMarker = '¤';

    private const string StrayParenMessage =
        "Unexpected ')' at the top level. There is no open '(' for it to close.";

    private const string StrayBraceMessage =
        "Unexpected '}' at the top level. There is no open '{' for it to close.";

    private const string StrayBracketMessage =
        "Unexpected ']' at the top level. There is no open '[' for it to close.";

    private static string MessageFor(char closer) => closer switch
    {
        ')' => StrayParenMessage,
        '}' => StrayBraceMessage,
        ']' => StrayBracketMessage,
        _ => throw new ArgumentOutOfRangeException(nameof(closer), closer, "Not a stray root closer."),
    };

    private static string Stray(string template, char closer) => template.Replace(StrayMarker, closer);

    private static string Control(string template) => template.Replace(StrayMarker, ' ');

    /// <summary>1-based (line, column) of every marker, in source order, by UTF-16 code unit.</summary>
    private static List<(int Line, int Column)> MarkerPositions(string template)
    {
        var positions = new List<(int Line, int Column)>();
        var line = 1;
        var column = 1;
        foreach (var unit in template)
        {
            if (unit == StrayMarker)
                positions.Add((line, column));

            if (unit == '\n')
            {
                line++;
                column = 1;
            }
            else
            {
                column++;
            }
        }

        return positions;
    }

    // `[Code] start-end message`, the end exclusive (a one-character closer at column c reads `c-(c + 1)`).
    private static string Describe(Diagnostic diagnostic)
    {
        var span = Assert.NotNull(diagnostic.Span);
        return $"[{diagnostic.Code}] {span.Start.Line}:{span.Start.Column}-{span.End.Line}:{span.End.Column} {diagnostic.Message}";
    }

    /// <summary>
    /// The source text covered by a single-line span under the half-open
    /// 1-based line/column convention (UTF-16 code units, like the lexer).
    /// </summary>
    private static string SourceSlice(string source, SourceSpan span)
    {
        Assert.Equal(span.Start.Line, span.End.Line);
        var line = source.Split('\n')[span.Start.Line - 1];
        return line.Substring(span.Start.Column - 1, span.End.Column - span.Start.Column);
    }

    private static void AssertStrayDiagnostic(Diagnostic diagnostic, char closer, int line, int column, string source)
    {
        Assert.Equal(MessageFor(closer), diagnostic.Message);
        Assert.Equal(DiagnosticCode.UnexpectedToken, diagnostic.Code);
        Assert.Equal(DiagnosticSeverity.Error, diagnostic.Severity);
        // The one-character closer: a half-open span one column wide.
        Assert.Equal(new SourceSpan(line, column, line, column + 1), diagnostic.Span);
        Assert.Equal(closer.ToString(), SourceSlice(source, Assert.NotNull(diagnostic.Span)));
    }

    /// <summary>
    /// Whole-root structural equality: the span-free Lean encoding of the two
    /// trees (declarations, parameter channels, opens, rows, nested bodies)
    /// plus root declaration, open-target, and output-row spans — the control
    /// preserves positions, so those spans must match exactly.
    /// </summary>
    private static void AssertSameRoot(Algorithm expected, Algorithm actual)
    {
        Assert.Equal(LeanAstEncoder.EncodeProgram(expected), LeanAstEncoder.EncodeProgram(actual));

        var expectedUser = Assert.IsType<Algorithm.User>(expected);
        var actualUser = Assert.IsType<Algorithm.User>(actual);
        Assert.Equal(
            expectedUser.Properties.Select(p => $"{p.Name} {string.Join(" ", p.DeclarationSpans)}"),
            actualUser.Properties.Select(p => $"{p.Name} {string.Join(" ", p.DeclarationSpans)}"));
        Assert.Equal(expectedUser.Output.Select(row => row.Span), actualUser.Output.Select(row => row.Span));
        Assert.Equal(expectedUser.Opens.Select(open => open.Span), actualUser.Opens.Select(open => open.Span));
    }

    private static void AssertRecoveredLikeControl(
        string source,
        char closer,
        IReadOnlyList<(int Line, int Column)> strayPositions,
        IReadOnlyList<Diagnostic> strayDiagnostics,
        Algorithm strayRoot,
        IReadOnlyList<Diagnostic> controlDiagnostics,
        Algorithm controlRoot)
    {
        // Exactly one diagnostic per stray token, spanning that token, in KatLang
        // terms; every other diagnostic is the control document's own, in the
        // control's order (a same-scope invariant such as a duplicate name is
        // still enforced across the recovery boundary).
        var strayOnly = strayDiagnostics.Where(d => d.Message == MessageFor(closer)).ToList();
        Assert.Equal(strayPositions.Count, strayOnly.Count);
        for (var i = 0; i < strayPositions.Count; i++)
            AssertStrayDiagnostic(strayOnly[i], closer, strayPositions[i].Line, strayPositions[i].Column, source);

        Assert.Equal(
            controlDiagnostics.Select(Describe),
            strayDiagnostics.Where(d => d.Message != MessageFor(closer)).Select(Describe));

        AssertSameRoot(controlRoot, strayRoot);
    }

    // ── Retention: the central regression ───────────────────────────────────

    /// <summary>
    /// The central K5-R3 assertion, deliberately independent of the diagnostic
    /// wording: everything after the stray token survives in its correct role.
    /// Before the recovery this failed with only <c>Before</c> in the tree.
    /// </summary>
    [Theory]
    [InlineData(')')]
    [InlineData('}')]
    [InlineData(']')]
    public void StrayCloserBetweenDeclarations_RetainsEveryLaterRootItem(char closer)
    {
        var source = $"Before = 1\n{closer}\nAfter = 2\nAfter";
        var parsed = SourceProvenance.ParseAllowingDiagnostics(source);
        Assert.True(parsed.HasFrontEndErrors);

        var root = Assert.IsType<Algorithm.User>(parsed.Root);
        Assert.Equal(new[] { "Before", "After" }, root.Properties.Select(p => p.Name));
        Assert.Equal(new SourceSpan(1, 1, 1, 7), Assert.Single(root.Properties[0].DeclarationSpans));
        Assert.Equal(new SourceSpan(3, 1, 3, 6), Assert.Single(root.Properties[1].DeclarationSpans));

        var after = Assert.IsType<Expr.Resolve>(Assert.Single(root.Output));
        Assert.Equal("After", after.Name);
        Assert.Equal(new SourceSpan(4, 1, 4, 6), after.Span);

        // `Before`'s body is exactly `1`: nothing after the stray token was
        // absorbed into the earlier property, and the root gained no parameter.
        var before = Assert.IsType<Algorithm.User>(root.Properties[0].Value);
        Assert.Equal(1, Assert.IsType<Expr.Num>(Assert.Single(before.Output)).Value);
        Assert.Empty(root.Params);
        Assert.Equal(2, Assert.IsType<Expr.Num>(Assert.Single(Assert.IsType<Algorithm.User>(root.Properties[1].Value).Output)).Value);
    }

    // ── Row-boundary matrix against the whitespace control ──────────────────

    public static TheoryData<string, string, char> RowBoundaryCases()
    {
        var data = new TheoryData<string, string, char>();
        foreach (var closer in new[] { ')', '}', ']' })
        {
            // Position: beginning, between complete root items, line-final, end.
            data.Add("leading", "¤\nBefore = 1\nAfter = 2\nAfter", closer);
            data.Add("between-declarations", "Before = 1\n¤\nAfter = 2\nAfter", closer);
            data.Add("line-final-after-definition-body", "Before = 1 ¤\nAfter = 2\nAfter", closer);
            data.Add("between-output-rows", "Before = 1\nBefore\n¤\nAfter = 2\nAfter", closer);
            data.Add("trailing-on-own-line", "Before = 1\nAfter = 2\nAfter\n¤", closer);
            data.Add("trailing-line-final", "Before = 1\nBefore ¤", closer);
            data.Add("leading-then-string-row", "¤ 'text'\nAfter = 2\nAfter", closer);

            // Consecutive closers and several recovery points in one document.
            data.Add("consecutive", "Before = 1\n¤¤¤\nAfter = 2\nAfter", closer);
            data.Add("multiple-recovery-points", "¤\nBefore = 1\n¤\nAfter = Before + 1\n¤\nAfter\n¤", closer);

            // Whole-root semantics across the recovery boundary.
            data.Add("cross-boundary-reference", "Base = 1\n¤\nNext = Base + 1\nNext", closer);
            data.Add("duplicate-name-across-boundary", "A = 1\n¤\nA = 2\nA", closer);
            data.Add("open-after-stray", "¤\nopen Math\nPi", closer);
            data.Add("duplicate-open-across-boundary", "open Math\n¤\nopen Math\nPi", closer);
            data.Add("open-after-property", "A = 1\n¤\nopen Math\nPi", closer);
            data.Add("open-after-output", "1\n¤\nopen Math\nPi", closer);
            data.Add("implicit-forwarding-to-later-sibling", "Use = Later\n¤\nLater = x + y\nUse", closer);
            data.Add("deconstruction-across-boundary", "a, b = 1, 2\n¤\nc, d = 3, 4\na, b, c, d", closer);
            data.Add("clause-family-across-boundary", "F(0) = 1\n¤\nF(x) = x\nF(2)", closer);
            data.Add("explicit-parameters-across-boundary", "Add(a, b) = a + b\n¤\nUse(v) = Add(v, 1)\nUse(2)", closer);

            // Valid nested constructs still close normally before a stray root closer.
            data.Add("valid-group-and-block-then-stray", "G = (1, 2)\n¤\nB = { 3 }\nG, B", closer);
            data.Add("valid-nested-constructs-line-final", "G = (1, 2) ¤\nB = { 3 } ¤\nG, B", closer);
            data.Add(
                "many-nested-constructs-then-stray",
                "G = (1, (2, 3))\nB = { C = { 4 }\n C }\nCall(x) = x\nD = Call((5)) + Call{6}\nL = [7, [8]]\n¤\nG, B, D, L",
                closer);

            // Location coverage beyond ASCII: supplementary-plane text before the
            // closer on its line (two UTF-16 units per character), and non-ASCII
            // identifiers on both sides of the recovery point.
            data.Add("supplementary-plane-string-before-closer", "S = '\U0001D538\U0001D539' ¤\nÄfter = 2\nÄfter", closer);
            data.Add("non-ascii-identifiers", "Größe = 1\n¤\nWert = Größe + 1\nWert", closer);
        }

        return data;
    }

    [Theory]
    [MemberData(nameof(RowBoundaryCases))]
    public void RowBoundaryStrayCloser_ReproducesTheControlDocument(string label, string template, char closer)
    {
        Assert.Contains(StrayMarker, template);
        var source = Stray(template, closer);
        var control = Control(template);
        var positions = MarkerPositions(template);

        // Raw syntax boundary.
        var straySyntax = Parser.ParseSyntax(source);
        var controlSyntax = Parser.ParseSyntax(control);
        // The control must itself meet the fixture's intended contract. Equality
        // alone could pass if both inputs returned the same error placeholder.
        DiagnosticCode[] expectedControlCodes = label switch
        {
            "duplicate-name-across-boundary" => [DiagnosticCode.DuplicateProperty],
            "duplicate-open-across-boundary" or "open-after-property" or "open-after-output"
                => [DiagnosticCode.InvalidOpenDeclaration],
            _ => [],
        };
        Assert.Equal(expectedControlCodes, controlSyntax.Diagnostics.Select(d => d.Code));
        Assert.True(straySyntax.HasErrors, label);
        AssertRecoveredLikeControl(
            source, closer, positions,
            straySyntax.Diagnostics, straySyntax.Root,
            controlSyntax.Diagnostics, controlSyntax.Root);

        // Public elaborating path — the ParseResult editor tooling consumes.
        // Parameter detection and implicit-argument resolution ran over ONE root
        // scope, so cross-boundary references, explicit parameter lists, and
        // clause families elaborate exactly as in the control.
        var strayParsed = SourceProvenance.ParseAllowingDiagnostics(source);
        var controlParsed = SourceProvenance.ParseAllowingDiagnostics(control);
        Assert.Equal(expectedControlCodes, controlParsed.Diagnostics.Select(d => d.Code));
        Assert.True(strayParsed.HasFrontEndErrors, label);
        AssertRecoveredLikeControl(
            source, closer, positions,
            strayParsed.Diagnostics, strayParsed.Root,
            controlParsed.Diagnostics, controlParsed.Root);
    }

    [Fact]
    public void MixedStrayClosers_EachReportTheirOwnCharacter_AndTheTailSurvives()
    {
        const string source = "Before = 1\n)}]}))\nAfter = 2\nAfter";
        var parsed = Parser.ParseSyntax(source);

        Assert.Equal(
            new[]
            {
                "[UnexpectedToken] 2:1-2:2 " + StrayParenMessage,
                "[UnexpectedToken] 2:2-2:3 " + StrayBraceMessage,
                "[UnexpectedToken] 2:3-2:4 " + StrayBracketMessage,
                "[UnexpectedToken] 2:4-2:5 " + StrayBraceMessage,
                "[UnexpectedToken] 2:5-2:6 " + StrayParenMessage,
                "[UnexpectedToken] 2:6-2:7 " + StrayParenMessage,
            },
            parsed.Diagnostics.Select(Describe));

        var controlSyntax = Parser.ParseSyntax("Before = 1\n      \nAfter = 2\nAfter");
        Assert.False(controlSyntax.HasErrors);
        AssertSameRoot(controlSyntax.Root, parsed.Root);
    }

    [Fact]
    public async Task AsyncParse_SharesTheRootRecovery()
    {
        // Parser.Parse and Parser.ParseAsync both enter the ONE raw syntax
        // boundary; one async case proves the recovery is not path-specific.
        const string source = "Before = 1\n)\nAfter = 2\nAfter";
        var sync = SourceProvenance.ParseAllowingDiagnostics(source);
        var asyncResult = await Parser.ParseAsync(source);

        Assert.True(asyncResult.HasErrors);
        Assert.Equal(sync.Diagnostics.Select(Describe), asyncResult.Diagnostics.Select(Describe));
        AssertSameRoot(sync.Root, asyncResult.Root);
    }

    // ── Mid-row closer and nested-construct controls ────────────────────────

    [Fact]
    public void StrayCloserInsideARow_EndsTheRowAndTheRestOfTheLineStartsANewRow()
    {
        // `A = 1 ) 2`: the closer ends A's body at `1`; `2` becomes a new ROOT
        // output row (never absorbed into the property body), followed by the
        // `A` row. This is the one shape where the whitespace control differs:
        // `A = 1   2` reports a missing separator and recovers both slots inside A.
        var parsed = Parser.ParseSyntax("A = 1 ) 2\nA");

        Assert.Equal(new[] { "[UnexpectedToken] 1:7-1:8 " + StrayParenMessage }, parsed.Diagnostics.Select(Describe));
        var root = Assert.IsType<Algorithm.User>(parsed.Root);
        var a = Assert.IsType<Algorithm.User>(Assert.Single(root.Properties).Value);
        Assert.Equal(1, Assert.IsType<Expr.Num>(Assert.Single(a.Output)).Value);
        Assert.Equal(2, root.Output.Count);
        Assert.Equal(2, Assert.IsType<Expr.Num>(root.Output[0]).Value);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(root.Output[1]).Name);
    }

    [Fact]
    public void MissingNestedCloser_IsUnchangedByRootRecovery()
    {
        // `(1` never closes: the declaration inside the still-open group is
        // rejected and the group reports its missing ')' at end of input. No
        // closer ever reaches the root, so nothing here is recovery-specific.
        var parsed = Parser.ParseSyntax("(1\nB = 2\nB");

        Assert.Equal(
            new[]
            {
                "[DeclarationInParentheses] 2:1-2:2 A property declaration is not allowed inside parentheses. Use a `{ ... }` block for a scoped algorithm.",
                "[UnexpectedToken] 3:2-3:2 Expected ')' but found end of input.",
            },
            parsed.Diagnostics.Select(Describe));

        var root = Assert.IsType<Algorithm.User>(parsed.Root);
        Assert.Empty(root.Properties);
        var recovery = Assert.IsType<Algorithm.User>(
            Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(root.Output)).Algorithm);
        Assert.Equal(new[] { "B" }, recovery.Properties.Select(p => p.Name));
        Assert.Equal(2, recovery.Output.Count);
    }

    [Fact]
    public void MismatchedNestedBraceCloser_ClosesTheBlock_ThenTheOrphanRecoversAtTheRoot()
    {
        // `{ 1 ) 2 }`: the block ends at the FIRST closer and reports the
        // mismatch. No construct is waiting for that ')', so it closes the block
        // it was written in (the delimiter-ownership law, #9) instead of becoming
        // a second, root-level report; the '}' it orphaned reaches the root, where
        // it IS unmatched, and is recovered in place, so `2` and `3` survive as
        // root rows.
        var parsed = Parser.ParseSyntax("{ 1 ) 2 }\n3");

        Assert.Equal(
            new[]
            {
                "[UnexpectedToken] 1:5-1:6 Expected '}' but found ')'.",
                "[UnexpectedToken] 1:9-1:10 " + StrayBraceMessage,
            },
            parsed.Diagnostics.Select(Describe));

        var root = Assert.IsType<Algorithm.User>(parsed.Root);
        Assert.Empty(root.Properties);
        Assert.Equal(3, root.Output.Count);
        var block = Assert.IsType<Algorithm.User>(Assert.IsType<Expr.AlgorithmExpr>(root.Output[0]).Algorithm);
        Assert.Equal(1, Assert.IsType<Expr.Num>(Assert.Single(block.Output)).Value);
        Assert.Equal(2, Assert.IsType<Expr.Num>(root.Output[1]).Value);
        Assert.Equal(3, Assert.IsType<Expr.Num>(root.Output[2]).Value);
    }

    [Fact]
    public void MismatchedNestedParenCloser_ClosesTheGroup_AndTheLaterSourceSurvives()
    {
        // `(1 }`: the group reports the mismatch at the '}', and since nothing is
        // waiting for a '}', that closer closes the group — one diagnostic — so the
        // later declaration and output row survive at the root.
        var parsed = Parser.ParseSyntax("(1 }\nB = 2\nB");

        Assert.Equal(
            new[]
            {
                "[UnexpectedToken] 1:4-1:5 Expected ')' but found '}'.",
            },
            parsed.Diagnostics.Select(Describe));

        var root = Assert.IsType<Algorithm.User>(parsed.Root);
        Assert.Equal(new[] { "B" }, root.Properties.Select(p => p.Name));
        Assert.Equal(new SourceSpan(2, 1, 2, 2), Assert.Single(root.Properties[0].DeclarationSpans));
        Assert.Equal(2, root.Output.Count);
        Assert.Equal(1, Assert.IsType<Expr.Num>(root.Output[0]).Value);
        Assert.Equal("B", Assert.IsType<Expr.Resolve>(root.Output[1]).Name);
    }

    // ── An OWED closer is never consumed as junk ─────────────────────────────
    //
    // Final audit (September 2026): primary-expression recovery used to consume
    // whatever token it could not start an expression with — including the closer
    // an ENCLOSING construct was waiting for. A trailing comma or a missing operand
    // before `)`/`]`/`}` (`F(1, )`, `(1 + )`, `[1, ]`, `{1, }`) therefore ate the
    // construct's own closer, left it open to the end of the file, and swallowed
    // every later root declaration into it with cascading "declaration inside
    // parentheses" reports. The owner now closes at its written closer and later
    // declarations stay in the scope they were written in.

    [Theory]
    [InlineData("F(a) = a\nA = F(1, )\nB = 2\nC = 3\nA, B, C", "[UnexpectedToken] 2:10-2:11 Unexpected ')'.")]
    [InlineData("F(a) = a\nA = F(1, -)\nB = 2\nC = 3\nA, B, C", "[UnexpectedToken] 2:11-2:12 Unexpected ')'.")]
    [InlineData("F(a) = a\nA = (1, )\nB = 2\nC = 3\nA, B, C", "[UnexpectedToken] 2:9-2:10 Unexpected ')'.")]
    [InlineData("F(a) = a\nA = (1 + )\nB = 2\nC = 3\nA, B, C", "[UnexpectedToken] 2:10-2:11 Unexpected ')'.")]
    [InlineData("F(a) = a\nA = [1, ]\nB = 2\nC = 3\nA, B, C", "[UnexpectedToken] 2:9-2:10 Unexpected ']'.")]
    [InlineData("F(a) = a\nA = {1, }\nB = 2\nC = 3\nA, B, C", "[UnexpectedToken] 2:9-2:10 Unexpected '}'.")]
    [InlineData("F(a) = a\nA = F(F(1, ), 2)\nB = 2\nC = 3\nA, B, C", "[UnexpectedToken] 2:12-2:13 Unexpected ')'.")]
    public void OwedCloserAfterAMissingOperand_ClosesTheConstruct_AndLaterDeclarationsSurvive(string source, string diagnostic)
    {
        var parsed = Parser.ParseSyntax(source);

        Assert.Equal(new[] { diagnostic }, parsed.Diagnostics.Select(Describe));
        var root = Assert.IsType<Algorithm.User>(parsed.Root);
        // Clause definitions are elaborated after the simple properties, so the family F
        // lists last; what matters is that every declaration is a ROOT property.
        Assert.Equal(new[] { "A", "B", "C", "F" }, root.Properties.Select(p => p.Name));
        Assert.Equal(new SourceSpan(3, 1, 3, 2), Assert.Single(root.Properties.Single(p => p.Name == "B").DeclarationSpans));
        Assert.Equal(new SourceSpan(4, 1, 4, 2), Assert.Single(root.Properties.Single(p => p.Name == "C").DeclarationSpans));
        Assert.Equal(3, root.Output.Count);
        Assert.Equal("A", Assert.IsType<Expr.Resolve>(root.Output[0]).Name);
    }

    /// <summary>
    /// Final audit (September 2026): the owed-closer rule must TERMINATE when the owed
    /// closer belongs to an OUTER construct of another kind. An enclosing list is waiting
    /// for `]` while a group or block body is still open (`[ (1, ]`, `[ {1 ]`): the primary
    /// parser leaves the owed `]` unconsumed, so the body loop must end at it — the group
    /// or block reports its own missing closer and the list closes at the `]`. (The first
    /// version of the rule looped forever here: the body loop ended only at `)`/`}`, and
    /// the editor fuzz corpus found the hang within minutes.) Later declarations survive
    /// as ROOT declarations and the parse stays linear.
    /// </summary>
    [Theory]
    [InlineData("A = [ (1, ]\nB = 2\nB", "[UnexpectedToken] 1:11-1:12 Unexpected ']'.", "[UnexpectedToken] 1:11-1:12 Expected ')' but found ']'.")]
    [InlineData("A = [ (1 ]\nB = 2\nB", "[UnexpectedToken] 1:10-1:11 Expected ')' but found ']'.")]
    [InlineData("A = [ {1, ]\nB = 2\nB", "[UnexpectedToken] 1:11-1:12 Unexpected ']'.", "[UnexpectedToken] 1:11-1:12 Expected '}' but found ']'.")]
    [InlineData("A = [ {1 ]\nB = 2\nB", "[UnexpectedToken] 1:10-1:11 Expected '}' but found ']'.")]
    [InlineData("A = [(]\nB = 2\nB", "[UnexpectedToken] 1:7-1:8 Expected ')' but found ']'.")]
    [InlineData("A = [ F(1, ]\nB = 2\nB", "[UnexpectedToken] 1:12-1:13 Unexpected ']'.", "[UnexpectedToken] 1:12-1:13 Expected ')' but found ']'.")]
    [InlineData("A = [ ( [ (1 ] ) ]\nB = 2\nB", "[UnexpectedToken] 1:14-1:15 Expected ')' but found ']'.")]
    [InlineData("A = ( [1, )\nB = 2\nB", "[UnexpectedToken] 1:11-1:12 Unexpected ')'.", "[UnexpectedToken] 1:11-1:12 Expected ']' but found ')'.")]
    [InlineData("A = { [1, }\nB = 2\nB", "[UnexpectedToken] 1:11-1:12 Unexpected '}'.", "[UnexpectedToken] 1:11-1:12 Expected ']' but found '}'.")]
    public void OwedCloserOfAnOuterConstructOfAnotherKind_EndsTheNestedBody_AndTheParseTerminates(
        string source, params string[] diagnostics)
    {
        var parsed = Parser.ParseSyntax(source);

        Assert.Equal(diagnostics, parsed.Diagnostics.Select(Describe));
        var root = Assert.IsType<Algorithm.User>(parsed.Root);
        Assert.Equal(new[] { "A", "B" }, root.Properties.Select(p => p.Name));
        Assert.Equal(new SourceSpan(2, 1, 2, 2), Assert.Single(root.Properties.Single(p => p.Name == "B").DeclarationSpans));
        Assert.Equal("B", Assert.IsType<Expr.Resolve>(Assert.Single(root.Output)).Name);
    }

    /// <summary>
    /// Exhaustive delimiter soup: EVERY string over the delimiter/separator/atom alphabet up
    /// to five characters parses to completion, with a diagnostic count linear in the input.
    /// Recovery in the parser is a set of non-consuming returns (an owed closer, the end of
    /// input) balanced by loops that must END at those tokens; this sweep is the executable
    /// statement that no combination of open and close delimiters re-enters a loop without
    /// consuming (the September 2026 audit's first owed-closer rule hung on `[ (1, ]`). The
    /// whole sweep is bounded by a wall-clock guard so a regression fails with the offending
    /// input instead of hanging the suite; the guard is awaited, never blocked on, so a
    /// diagnostic-count failure inside the sweep surfaces as itself rather than wrapped.
    /// <para>It also states the delimiter-ownership law's consequence (#9): every closer
    /// closes at least one open construct, so when a malformed source's delimiters balance
    /// by COUNT, whatever their kinds (`(1, 2]`, `{ 1 ) 2 }`, `[({[1)}]`), every construct
    /// it opens is closed within it, and a declaration written after it on a new line stays
    /// a declaration of the root — no wrong closer can leave a construct open to swallow
    /// the rest of the document.</para>
    /// </summary>
    [Fact]
    public async Task DelimiterSoup_AlwaysTerminates_WithLinearDiagnostics()
    {
        char[] alphabet = ['(', ')', '[', ']', '{', '}', ',', '1', ' ', '\n'];
        var current = "";
        var parsed = 0;
        var sweep = Task.Run(() =>
        {
            var buffer = new char[5];
            for (var length = 1; length <= 5; length++)
            {
                var combinations = (int)Math.Pow(alphabet.Length, length);
                for (var code = 0; code < combinations; code++)
                {
                    var rest = code;
                    for (var i = 0; i < length; i++)
                    {
                        buffer[i] = alphabet[rest % alphabet.Length];
                        rest /= alphabet.Length;
                    }
                    var source = new string(buffer, 0, length);
                    Volatile.Write(ref current, source);
                    var result = Parser.ParseSyntax(source);
                    Assert.True(
                        result.Diagnostics.Count <= 2 * length + 1,
                        $"{result.Diagnostics.Count} diagnostics for {length} characters: {Escape(source)}");
                    if (result.HasErrors && DelimitersBalanceByCount(source))
                    {
                        var withSuffix = Parser.ParseSyntax(source + "\nGood = 41\nGood");
                        var good = Assert.Single(withSuffix.Root.Properties, p => p.Name == "Good");
                        Assert.True(
                            Assert.Single(good.DeclarationSpans).Start.Line == source.Count(c => c == '\n') + 2,
                            $"The declaration after a count-balanced prefix was not kept at the root: {Escape(source)}");
                    }
                    parsed++;
                }
            }
        });

        var finished = await Task.WhenAny(sweep, Task.Delay(TimeSpan.FromMinutes(2)));
        Assert.True(
            finished == sweep,
            $"The delimiter sweep did not terminate; last input: {Escape(Volatile.Read(ref current))}");
        await sweep;
        Assert.Equal(111_110, parsed);

        static string Escape(string source) => source.Replace("\n", "\\n", StringComparison.Ordinal);

        // No prefix closes more delimiters than it opened, and the totals match — kinds ignored.
        static bool DelimitersBalanceByCount(string source)
        {
            var depth = 0;
            foreach (var c in source)
            {
                if (c is '(' or '[' or '{')
                    depth++;
                else if (c is ')' or ']' or '}' && --depth < 0)
                    return false;
            }

            return depth == 0;
        }
    }

    [Fact]
    public void OwedCloserRecovery_KeepsTheRecoveredSlotInsideTheConstruct()
    {
        // The missing operand becomes one placeholder slot of the SAME list; the
        // pinned `(3,)` family (LanguageSpec `trailing-comma-in-parens-rejected`)
        // keeps its UnexpectedToken code.
        var parsed = Parser.ParseSyntax("F(a, b) = a\nA = F(1, )\nA");
        var root = Assert.IsType<Algorithm.User>(parsed.Root);
        var body = Assert.IsType<Algorithm.User>(root.Properties.Single(p => p.Name == "A").Value);
        var call = Assert.IsType<Expr.Call>(Assert.Single(body.Output));
        Assert.Equal(2, call.Args.Count);
        Assert.Equal(1, Assert.IsType<Expr.Num>(call.Args[0]).Value);
        Assert.Equal(0, Assert.IsType<Expr.Num>(call.Args[1]).Value);
        Assert.Equal(DiagnosticCode.UnexpectedToken, Assert.Single(parsed.Diagnostics).Code);
    }

    [Fact]
    public void CloserNoConstructIsWaitingFor_ClosesTheInnermostOpenConstruct()
    {
        // A closer of another kind inside a brace body is not owed by anything. It is
        // never consumed as junk while a construct is open (#9): it closes the block it
        // was written in — one mismatch diagnostic — so a wrong closer can never leave
        // the block open to swallow later declarations. What follows it on the line is
        // explained by that diagnostic, and the block's own `}`, now orphaned, is a
        // root stray.
        var parsed = Parser.ParseSyntax("A = { 1, ) 2 }\nB = 2\nA, B");
        Assert.Equal(
            new[]
            {
                "[UnexpectedToken] 1:10-1:11 Expected '}' but found ')'.",
                "[UnexpectedToken] 1:14-1:15 " + StrayBraceMessage,
            },
            parsed.Diagnostics.Select(Describe));
        var root = Assert.IsType<Algorithm.User>(parsed.Root);
        Assert.Equal(new[] { "A", "B" }, root.Properties.Select(p => p.Name));
        var a = Assert.IsType<Algorithm.User>(root.Properties[0].Value);
        Assert.Equal(2, a.Output.Count);
        var block = Assert.IsType<Algorithm.User>(Assert.IsType<Expr.AlgorithmExpr>(a.Output[0]).Algorithm);
        Assert.Equal(2, block.Output.Count); // `1` and the missing slot's placeholder
        Assert.Equal(2, Assert.IsType<Expr.Num>(a.Output[1]).Value);

        // At the root nothing is open: `1, )` reports once and keeps parsing.
        var atRoot = Parser.ParseSyntax("1, )\nB = 2\nB");
        Assert.Equal(new[] { "[UnexpectedToken] 1:4-1:5 Unexpected ')'." }, atRoot.Diagnostics.Select(Describe));
        Assert.Equal(new[] { "B" }, Assert.IsType<Algorithm.User>(atRoot.Root).Properties.Select(p => p.Name));
    }

    [Fact]
    public void SemicolonRecovery_NeverClaimsTheNextDeclarationAsASlot()
    {
        // `;` is never expression syntax; its recovery consumes the `;` and stops at a
        // declaration head, a closer, or the end of input instead of parsing the next
        // line's `B = 2` as a slot (which tore the head apart and made `B` a parameter).
        var parsed = Parser.ParseSyntax("A = 1;\nB = 2\nA, B");
        Assert.Equal(DiagnosticCode.UnsupportedSemicolon, Assert.Single(parsed.Diagnostics).Code);
        var root = Assert.IsType<Algorithm.User>(parsed.Root);
        Assert.Equal(new[] { "A", "B" }, root.Properties.Select(p => p.Name));
        Assert.Equal(1, Assert.IsType<Expr.Num>(Assert.Single(Assert.IsType<Algorithm.User>(root.Properties[0].Value).Output)).Value);

        var sameLine = Parser.ParseSyntax("A = 1; B = 2\nA, B");
        Assert.Equal(DiagnosticCode.UnsupportedSemicolon, Assert.Single(sameLine.Diagnostics).Code);
        Assert.Equal(new[] { "A", "B" }, Assert.IsType<Algorithm.User>(sameLine.Root).Properties.Select(p => p.Name));

        // A following EXPRESSION row still recovers as the next slot (unchanged).
        var expression = Parser.ParseSyntax("A = 1;\n2\nA");
        Assert.Equal(DiagnosticCode.UnsupportedSemicolon, Assert.Single(expression.Diagnostics).Code);
        Assert.Equal(2, Assert.IsType<Algorithm.User>(Assert.IsType<Algorithm.User>(expression.Root).Properties[0].Value).Output.Count);
    }

    [Fact]
    public void StrayClosingBracket_RecoversLikeTheOtherRootClosers()
    {
        // ']' used to take the primary-expression fallback at a root row start: a
        // different message and an invented placeholder OUTPUT ROW. It is now one of
        // the three closers the root recovers uniformly (#9): reported in KatLang
        // terms at its own span, consumed, and no row is invented.
        var parsed = Parser.ParseSyntax("Before = 1\n]\nAfter = 2\nAfter");

        Assert.Equal(new[] { "[UnexpectedToken] 2:1-2:2 " + StrayBracketMessage }, parsed.Diagnostics.Select(Describe));
        var root = Assert.IsType<Algorithm.User>(parsed.Root);
        Assert.Equal(new[] { "Before", "After" }, root.Properties.Select(p => p.Name));
        Assert.Equal("After", Assert.IsType<Expr.Resolve>(Assert.Single(root.Output)).Name);
    }

    // ── Editor information over the recovered tree ──────────────────────────

    [Theory]
    [InlineData(')')]
    [InlineData('}')]
    [InlineData(']')]
    public void SemanticModel_DiscoversDeclarationsAndReferencesAfterTheStrayCloser(char closer)
    {
        var source = $"Before = 1\n{closer}\nAfter = Before + 1\nAfter";
        var parsed = SourceProvenance.ParseAllowingDiagnostics(source);
        Assert.True(parsed.HasFrontEndErrors);

        // Built despite the diagnostic, as an editor must.
        var model = SemanticModelBuilder.Build(parsed.Parsed);

        var declaration = Assert.Single(model.FindDeclarations("After"));
        Assert.Equal(new SourceSpan(3, 1, 3, 6), declaration.Span);
        Assert.Equal(OccurrenceKind.PropertyDefinition, declaration.Kind);

        // Go-to-definition from the final output row.
        var reference = Assert.IsType<IdentifierResolution>(model.FindResolutionAt(new SourcePosition(4, 3)));
        Assert.Equal(IdentifierClassification.PropertyReference, reference.Classification);
        Assert.Equal(new SourceSpan(4, 1, 4, 6), reference.Occurrence.Span);
        Assert.Equal(declaration, reference.ResolvedDeclaration);

        // The reference INSIDE the later body resolves across the recovery
        // boundary to the earlier sibling: one root scope, not an implicit parameter.
        var crossReference = Assert.IsType<IdentifierResolution>(model.FindResolutionAt(new SourcePosition(3, 9)));
        Assert.Equal(IdentifierClassification.PropertyReference, crossReference.Classification);
        Assert.Equal(new SourceSpan(3, 9, 3, 15), crossReference.Occurrence.Span);
        Assert.Equal(new SourceSpan(1, 1, 1, 7), crossReference.ResolvedDeclaration!.Span);

        // Hover/signature metadata for the later declaration.
        var property = Assert.Single(model.FindProperties("After"));
        Assert.Equal("After", property.DisplaySignature);
        Assert.Empty(property.Parameters);
        Assert.Equal(declaration, property.Declaration);

        // Completion at the final row sees both declarations.
        Assert.Equal(
            new[] { "After", "Before" },
            model.GetVisibleSymbolsAt(new SourcePosition(4, 1))
                .Where(symbol => symbol.Classification == IdentifierClassification.PropertyReference)
                .Select(symbol => symbol.Name)
                .Order());

        // Every listed site slices the document to the identifier written there.
        Assert.All(model.IdentifierOccurrences, occurrence => Assert.Equal(occurrence.Name, SourceSlice(source, occurrence.Span)));
        Assert.All(model.Declarations, occurrence => Assert.Equal(occurrence.Name, SourceSlice(source, occurrence.Span)));
    }

    [Fact]
    public void SemanticModel_KeepsUtf16Coordinates_AfterASupplementaryPlaneRow()
    {
        // `S = '𝔸𝔹' )`: two supplementary-plane characters (four code units)
        // precede the closer, and the later declaration is a non-ASCII name.
        const string source = "S = '\U0001D538\U0001D539' )\nÄfter = 2\nÄfter";
        var parsed = SourceProvenance.ParseAllowingDiagnostics(source);
        var diagnostic = Assert.Single(parsed.Diagnostics);
        AssertStrayDiagnostic(diagnostic, ')', 1, 12, source);

        var model = SemanticModelBuilder.Build(parsed.Parsed);
        var declaration = Assert.Single(model.FindDeclarations("Äfter"));
        Assert.Equal(new SourceSpan(2, 1, 2, 6), declaration.Span);

        var reference = Assert.IsType<IdentifierResolution>(model.FindResolutionAt(new SourcePosition(3, 1)));
        Assert.Equal(IdentifierClassification.PropertyReference, reference.Classification);
        Assert.Equal(new SourceSpan(3, 1, 3, 6), reference.Occurrence.Span);
        Assert.Equal(declaration, reference.ResolvedDeclaration);
        Assert.All(model.IdentifierOccurrences, occurrence => Assert.Equal(occurrence.Name, SourceSlice(source, occurrence.Span)));
    }

    // ── Error gating: the recovered remainder is never evaluated ────────────

    [Theory]
    [InlineData(')')]
    [InlineData('}')]
    [InlineData(']')]
    public async Task Engine_RejectsTheDocument_WithoutEvaluatingTheRecoveredRemainder(char closer)
    {
        // A ParseFailure alone does not prove that evaluation never ran: the
        // former additional-diagnostic evaluation after load failures returned
        // ParseFailure even after executing caller effects.
        // Observe execution directly, with a valid control proving the probe is live.
        const string template = "Before = 1\n¤\nAfter = Probe()\nAfter";
        var source = Stray(template, closer);
        var calls = 0;
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(HostOperation.Create("Probe", (_, _) =>
            {
                calls++;
                return new Result.Atom(2);
            })),
        };
        Assert.IsType<RunResult.Success>(KatLangEngine.Run(Control(template), options));
        Assert.Equal(1, calls);
        calls = 0;

        var failure = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source, options));
        var error = Assert.Single(failure.Errors);
        Assert.Equal(MessageFor(closer), error.Message);
        Assert.Equal(KatLangErrorCode.UnexpectedToken, error.Code);
        Assert.Null(error.Source); // front-end diagnostic, not an evaluation error
        Assert.Equal(new SourceSpan(2, 1, 2, 2), error.Span);
        Assert.Equal(0, calls);

        var asyncFailure = Assert.IsType<RunResult.ParseFailure>(await KatLangEngine.RunAsync(source, options));
        Assert.Equal(error.ToString(), Assert.Single(asyncFailure.Errors).ToString());
        Assert.Equal(0, calls);

        // A simultaneous load error must not enable the additional-error
        // evaluation path when the original syntax already contains an error.
        var loadingOptions = new RunOptions
        {
            HostOperations = options.HostOperations,
            AllowedHosts = ["katlang.org"],
            DownloadCode = (_, _) => throw new InvalidOperationException("Test download failure"),
        };
        var loadingFailure = Assert.IsType<RunResult.ParseFailure>(await KatLangEngine.RunAsync(
            source + "\nMissing = load('https://katlang.org/missing.kat')", loadingOptions));
        Assert.Contains(loadingFailure.Errors, e => e.Code == KatLangErrorCode.UnexpectedToken);
        Assert.Contains(loadingFailure.Errors, e => e.Message.Contains("load: failed to fetch"));
        Assert.Equal(0, calls);
    }

    // ── Robustness: progress, bounded diagnostics, linear work ─────────────

    [Fact]
    public void RunOfStrayClosers_TerminatesWithOneDiagnosticPerToken_AndRetainsTheTail()
    {
        const int count = 2000;
        var closers = string.Concat(Enumerable.Range(0, count).Select(i => i % 2 == 0 ? ")" : "}"));
        var source = $"Before = 1\n{closers}\nAfter = 2\nAfter";

        var parsed = Parser.ParseSyntax(source);

        Assert.Equal(count, parsed.Diagnostics.Count);
        for (var i = 0; i < count; i++)
            AssertStrayDiagnostic(parsed.Diagnostics[i], closers[i], 2, i + 1, source);

        var root = Assert.IsType<Algorithm.User>(parsed.Root);
        Assert.Equal(new[] { "Before", "After" }, root.Properties.Select(p => p.Name));
        Assert.Equal("After", Assert.IsType<Expr.Resolve>(Assert.Single(root.Output)).Name);
    }

    [Fact]
    public void RunOfStrayClosers_CostsLinearParserWork()
    {
        // Each recovery step consumes exactly one token, so the parser's own
        // token-step counter must grow linearly with the run: doubling the run
        // may at most 2.5x the steps (the bound ParserNestingDepthTests uses).
        static long Steps(int k)
        {
            var observations = new ParserTraversalObservations();
            var closers = string.Concat(Enumerable.Repeat(")}", k / 2));
            var result = Parser.ParseSyntaxObserved($"Before = 1\n{closers}\nAfter = 2\nAfter", observations);
            Assert.Equal(k, result.Diagnostics.Count);
            Assert.True(observations.TokenSteps >= k, "The observer must count consumed tokens; zero steps cannot prove linearity.");
            return observations.TokenSteps;
        }

        var steps20 = Steps(20_000);
        var steps40 = Steps(40_000);
        var steps80 = Steps(80_000);
        Assert.True(steps40 <= 2.5 * steps20, $"{steps20} -> {steps40} steps (20k -> 40k closers)");
        Assert.True(steps80 <= 2.5 * steps40, $"{steps40} -> {steps80} steps (40k -> 80k closers)");
    }
}
