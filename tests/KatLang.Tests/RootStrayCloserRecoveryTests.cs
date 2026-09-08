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
/// tree serves diagnostics and editor analysis only, never evaluation.
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

    private static string MessageFor(char closer) => closer switch
    {
        ')' => StrayParenMessage,
        '}' => StrayBraceMessage,
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

    private static string Describe(Diagnostic diagnostic)
        => $"[{diagnostic.Code}] {diagnostic.Span.StartLineNumber}:{diagnostic.Span.StartColumn}-"
            + $"{diagnostic.Span.EndLineNumber}:{diagnostic.Span.EndColumn} {diagnostic.Message}";

    /// <summary>
    /// The source text covered by a single-line span under the inclusive
    /// 1-based line/column convention (UTF-16 code units, like the lexer).
    /// </summary>
    private static string SourceSlice(string source, SourceSpan span)
    {
        Assert.Equal(span.StartLineNumber, span.EndLineNumber);
        var line = source.Split('\n')[span.StartLineNumber - 1];
        return line.Substring(span.StartColumn - 1, span.EndColumn - span.StartColumn + 1);
    }

    private static void AssertStrayDiagnostic(Diagnostic diagnostic, char closer, int line, int column, string source)
    {
        Assert.Equal(MessageFor(closer), diagnostic.Message);
        Assert.Equal(DiagnosticCode.UnexpectedToken, diagnostic.Code);
        Assert.Equal(DiagnosticSeverity.Error, diagnostic.Severity);
        Assert.Equal(new SourceSpan(line, column, line, column), diagnostic.Span);
        Assert.Equal(closer.ToString(), SourceSlice(source, diagnostic.Span));
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
    public void StrayCloserBetweenDeclarations_RetainsEveryLaterRootItem(char closer)
    {
        var source = $"Before = 1\n{closer}\nAfter = 2\nAfter";
        var parsed = SourceProvenance.ParseAllowingDiagnostics(source);
        Assert.True(parsed.HasFrontEndErrors);

        var root = Assert.IsType<Algorithm.User>(parsed.Root);
        Assert.Equal(new[] { "Before", "After" }, root.Properties.Select(p => p.Name));
        Assert.Equal(new SourceSpan(1, 1, 1, 6), Assert.Single(root.Properties[0].DeclarationSpans));
        Assert.Equal(new SourceSpan(3, 1, 3, 5), Assert.Single(root.Properties[1].DeclarationSpans));

        var after = Assert.IsType<Expr.Resolve>(Assert.Single(root.Output));
        Assert.Equal("After", after.Name);
        Assert.Equal(new SourceSpan(4, 1, 4, 5), after.Span);

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
        foreach (var closer in new[] { ')', '}' })
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
        const string source = "Before = 1\n)}}))\nAfter = 2\nAfter";
        var parsed = Parser.ParseSyntax(source);

        Assert.Equal(
            new[]
            {
                "[UnexpectedToken] 2:1-2:1 " + StrayParenMessage,
                "[UnexpectedToken] 2:2-2:2 " + StrayBraceMessage,
                "[UnexpectedToken] 2:3-2:3 " + StrayBraceMessage,
                "[UnexpectedToken] 2:4-2:4 " + StrayParenMessage,
                "[UnexpectedToken] 2:5-2:5 " + StrayParenMessage,
            },
            parsed.Diagnostics.Select(Describe));

        var controlSyntax = Parser.ParseSyntax("Before = 1\n     \nAfter = 2\nAfter");
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
        // `A = 1   2` would be the adjacency body `A = 1, 2`.
        var parsed = Parser.ParseSyntax("A = 1 ) 2\nA");

        Assert.Equal(new[] { "[UnexpectedToken] 1:7-1:7 " + StrayParenMessage }, parsed.Diagnostics.Select(Describe));
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
                "[DeclarationInParentheses] 2:1-2:1 A property declaration is not allowed inside parentheses. Use a `{ ... }` block for a scoped algorithm.",
                "[UnexpectedToken] 3:2-3:2 Expected 'RParen', got 'EndOfFile'.",
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
    public void MismatchedNestedBraceCloser_KeepsItsDiagnostic_ThenTheOrphansRecoverAtTheRoot()
    {
        // `{ 1 ) 2 }`: the block ends at the FIRST closer and reports the
        // mismatch exactly as before. That ')' then reaches the root, where it
        // IS unmatched, and is recovered in place together with the '}' it
        // orphaned, so `2` and `3` survive as root rows. (Before the recovery
        // the second diagnostic read "Expected end of input" and both rows were
        // dropped — the one directly related change to a malformed-nesting shape.)
        var parsed = Parser.ParseSyntax("{ 1 ) 2 }\n3");

        Assert.Equal(
            new[]
            {
                "[UnexpectedToken] 1:5-1:5 Expected 'RBrace', got 'RParen'.",
                "[UnexpectedToken] 1:5-1:5 " + StrayParenMessage,
                "[UnexpectedToken] 1:9-1:9 " + StrayBraceMessage,
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
    public void MismatchedNestedParenCloser_KeepsItsDiagnostic_ThenTheOrphanRecoversAtTheRoot()
    {
        // `(1 }`: the group reports the mismatch at the '}' (unchanged); the
        // '}' then reaches the root and is recovered, so the later declaration
        // and output row survive.
        var parsed = Parser.ParseSyntax("(1 }\nB = 2\nB");

        Assert.Equal(
            new[]
            {
                "[UnexpectedToken] 1:4-1:4 Expected 'RParen', got 'RBrace'.",
                "[UnexpectedToken] 1:4-1:4 " + StrayBraceMessage,
            },
            parsed.Diagnostics.Select(Describe));

        var root = Assert.IsType<Algorithm.User>(parsed.Root);
        Assert.Equal(new[] { "B" }, root.Properties.Select(p => p.Name));
        Assert.Equal(new SourceSpan(2, 1, 2, 1), Assert.Single(root.Properties[0].DeclarationSpans));
        Assert.Equal(2, root.Output.Count);
        Assert.Equal(1, Assert.IsType<Expr.Num>(root.Output[0]).Value);
        Assert.Equal("B", Assert.IsType<Expr.Resolve>(root.Output[1]).Name);
    }

    [Fact]
    public void StrayClosingBracket_KeepsItsOwnRecoveryPath()
    {
        // ']' is a different token class: it already recovered through the
        // primary-expression fallback (a placeholder row) and is out of scope
        // here. Pinned so the root closer recovery is provably not widened.
        var parsed = Parser.ParseSyntax("Before = 1\n]\nAfter = 2\nAfter");

        Assert.Equal(new[] { "[UnexpectedToken] 2:1-2:1 Unexpected token: 'RBracket'." }, parsed.Diagnostics.Select(Describe));
        var root = Assert.IsType<Algorithm.User>(parsed.Root);
        Assert.Equal(new[] { "Before", "After" }, root.Properties.Select(p => p.Name));
        Assert.Equal(2, root.Output.Count);
    }

    // ── Editor information over the recovered tree ──────────────────────────

    [Theory]
    [InlineData(')')]
    [InlineData('}')]
    public void SemanticModel_DiscoversDeclarationsAndReferencesAfterTheStrayCloser(char closer)
    {
        var source = $"Before = 1\n{closer}\nAfter = Before + 1\nAfter";
        var parsed = SourceProvenance.ParseAllowingDiagnostics(source);
        Assert.True(parsed.HasFrontEndErrors);

        // Built despite the diagnostic, as an editor must.
        var model = SemanticModelBuilder.Build(parsed.Parsed);

        var declaration = Assert.Single(model.FindDeclarations("After"));
        Assert.Equal(new SourceSpan(3, 1, 3, 5), declaration.Span);
        Assert.Equal(OccurrenceKind.PropertyDefinition, declaration.Kind);

        // Go-to-definition from the final output row.
        var reference = Assert.IsType<IdentifierResolution>(model.FindResolutionAt(4, 3));
        Assert.Equal(IdentifierClassification.PropertyReference, reference.Classification);
        Assert.Equal(new SourceSpan(4, 1, 4, 5), reference.Occurrence.Span);
        Assert.Equal(declaration, reference.ResolvedDeclaration);

        // The reference INSIDE the later body resolves across the recovery
        // boundary to the earlier sibling: one root scope, not an implicit parameter.
        var crossReference = Assert.IsType<IdentifierResolution>(model.FindResolutionAt(3, 9));
        Assert.Equal(IdentifierClassification.PropertyReference, crossReference.Classification);
        Assert.Equal(new SourceSpan(3, 9, 3, 14), crossReference.Occurrence.Span);
        Assert.Equal(new SourceSpan(1, 1, 1, 6), crossReference.ResolvedDeclaration!.Span);

        // Hover/signature metadata for the later declaration.
        var property = Assert.Single(model.FindProperties("After"));
        Assert.Equal("After", property.DisplaySignature);
        Assert.Empty(property.Parameters);
        Assert.Equal(declaration, property.Declaration);

        // Completion at the final row sees both declarations.
        Assert.Equal(
            new[] { "After", "Before" },
            model.GetVisibleSymbolsAt(4, 1)
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
        Assert.Equal(new SourceSpan(2, 1, 2, 5), declaration.Span);

        var reference = Assert.IsType<IdentifierResolution>(model.FindResolutionAt(3, 1));
        Assert.Equal(IdentifierClassification.PropertyReference, reference.Classification);
        Assert.Equal(new SourceSpan(3, 1, 3, 5), reference.Occurrence.Span);
        Assert.Equal(declaration, reference.ResolvedDeclaration);
        Assert.All(model.IdentifierOccurrences, occurrence => Assert.Equal(occurrence.Name, SourceSlice(source, occurrence.Span)));
    }

    // ── Error gating: the recovered remainder is never evaluated ────────────

    [Theory]
    [InlineData(')')]
    [InlineData('}')]
    public async Task Engine_RejectsTheDocument_WithoutEvaluatingTheRecoveredRemainder(char closer)
    {
        // A ParseFailure alone does not prove that evaluation never ran: the
        // engine can evaluate after some load failures for additional diagnostics.
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
        Assert.Equal((2, 1, 2, 1), (error.StartLine, error.StartColumn, error.EndLine, error.EndColumn));
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
