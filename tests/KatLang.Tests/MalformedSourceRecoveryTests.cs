using KatLang.Semantics;
using KatLang.Tests.LanguageSpec;

namespace KatLang.Tests;

/// <summary>
/// #9 invalid-program / parser-recovery audit (September 2026): the recovery laws the
/// audit established, each pinned at the one parser mechanism that owns it. Invalid
/// syntax may produce diagnostics and a recovery tree, but recovery never invents a
/// different program, never takes syntax an enclosing construct owns, never swallows
/// later independent source, and never lets an invalid document evaluate.
/// <list type="bullet">
/// <item>DELIMITER OWNERSHIP: a closing delimiter is never consumed as junk while a
/// construct is open. The innermost construct resolves it — its own closer is consumed,
/// one an enclosing construct owes is left for that owner, one nothing is waiting for
/// closes the innermost construct as its mismatched closer — so every closer closes at
/// least one construct, and a region whose delimiters balance by count cannot leave a
/// construct open to swallow the rest of the document.</item>
/// <item>A DECLARATION HEAD IS NEVER AN OPERAND: a line ending in an incomplete
/// expression (a trailing operator, `,`, `:`, `.`, prefix `-`/`not`, or an empty
/// definition body) never takes the next line's declaration head as its continuation;
/// the dangling token is the one error and the declaration keeps its scope.</item>
/// <item>CLAUSE-HEAD CONFINEMENT: a recognized head's recovery stays inside its own
/// parentheses — the head's `)`, `=`, and body are found where written — and a head whose
/// pattern needed recovery takes part in no cross-clause family check.</item>
/// <item>REPORTED CHARACTERS ARE INVISIBLE TO THE GRAMMAR: the parser skips a character
/// the lexer reported exactly like a comment, so the lexer's diagnostic is its only one and
/// every grammar decision is made as if it were not there; where the grammar needs a piece
/// exactly where it stands (an operand, a member name, an open target, a pattern item, a
/// separating comma — never a closer or `=`), the character is that piece, filled
/// silently.</item>
/// <item>RECOVERY SHAPES are shapes a valid program can have (no two collecting bindings
/// at one level), so every downstream consumer — the semantic model included — accepts
/// them.</item>
/// </list>
/// Sources here are malformed by design, so the raw syntax boundary and the permissive
/// <see cref="SourceProvenance.ParseAllowingDiagnostics"/> path are used deliberately.
/// </summary>
public class MalformedSourceRecoveryTests
{
    // `[Code] start-end message`, end exclusive.
    private static string Describe(Diagnostic diagnostic)
    {
        var span = Assert.NotNull(diagnostic.Span);
        return $"[{diagnostic.Code}] {span.Start.Line}:{span.Start.Column}-{span.End.Line}:{span.End.Column} {diagnostic.Message}";
    }

    private static Property RootProperty(Algorithm.User root, string name)
        => Assert.Single(root.Properties, property => property.Name == name);

    // ── Delimiter ownership: a wrong closer closes the construct it was written in ──

    public static TheoryData<string, string, string, int> WrongCloserCases() => new()
    {
        // source, the one diagnostic, the declaration that must survive, its line
        { "(1, 2]\nB = 2\nB", "[UnexpectedToken] 1:6-1:7 Expected ')' but found ']'.", "B", 2 },
        { "(1 ]\nB = 2\nB", "[UnexpectedToken] 1:4-1:5 Expected ')' but found ']'.", "B", 2 },
        { "[1, 2)\nB = 2\nB", "[UnexpectedToken] 1:6-1:7 Expected ']' but found ')'.", "B", 2 },
        { "{1, 2]\nB = 2\nB", "[UnexpectedToken] 1:6-1:7 Expected '}' but found ']'.", "B", 2 },
        { "(1, 2}\nB = 2\nB", "[UnexpectedToken] 1:6-1:7 Expected ')' but found '}'.", "B", 2 },
        { "F(a, b) = a + b\nX = F((1, 2], 3)\nLater = 2\nLater", "[UnexpectedToken] 2:12-2:13 Expected ')' but found ']'.", "Later", 3 },
        { "A = (1, ]\nLater = 2\nLater", "[UnexpectedToken] 1:9-1:10 Expected ')' but found ']'.", "Later", 2 },
        { "A = [1, )\nLater = 2\nLater", "[UnexpectedToken] 1:9-1:10 Expected ']' but found ')'.", "Later", 2 },
    };

    [Theory]
    [MemberData(nameof(WrongCloserCases))]
    public void WrongCloser_ClosesItsConstruct_AndLaterDeclarationsSurvive(string source, string diagnostic, string survivor, int line)
    {
        // Before #9 a `]` (and, after a comma, any closer) that nothing was waiting for
        // was consumed as junk: the construct stayed open to the end of the file and every
        // later declaration became a "declaration inside parentheses".
        var parsed = Parser.ParseSyntax(source);
        Assert.Equal(new[] { diagnostic }, parsed.Diagnostics.Select(Describe));
        Assert.Equal(line, Assert.Single(RootProperty(parsed.Root, survivor).DeclarationSpans).Start.Line);
    }

    [Fact]
    public void WrongCloserInsideABlock_KeepsTheLaterDeclarationInTheBlockItWasWrittenIn()
    {
        var parsed = Parser.ParseSyntax("X = { A = (1, 2]\nLater = 5 }\nLater");
        Assert.Equal(new[] { "[UnexpectedToken] 1:16-1:17 Expected ')' but found ']'." }, parsed.Diagnostics.Select(Describe));
        var x = Assert.IsType<Algorithm.User>(RootProperty(parsed.Root, "X").Value);
        Assert.Equal(new[] { "A", "Later" }, x.Properties.Select(p => p.Name));
        Assert.IsType<Expr.Capture>(Assert.Single(x.Properties[0].Value.Output));
    }

    [Fact]
    public void OwedCloser_IsStillLeftForItsOwner()
    {
        // The group's wrong closer IS the enclosing list's: the group reports its missing
        // ')' and the list closes there (unchanged by #9); what remains is a root stray.
        var parsed = Parser.ParseSyntax("X = [1, (2, 3], 4]\nB = 2\nB");
        Assert.Equal(
            new[]
            {
                "[UnexpectedToken] 1:14-1:15 Expected ')' but found ']'.",
                "[UnexpectedToken] 1:18-1:19 Unexpected ']' at the top level. There is no open '[' for it to close.",
            },
            parsed.Diagnostics.Select(Describe));
        Assert.Equal(2, Assert.Single(RootProperty(parsed.Root, "B").DeclarationSpans).Start.Line);
    }

    [Theory]
    // A closer an ENCLOSING construct owes is never taken by a clause head or its
    // recovery: before #9 the pattern parser consumed it (`Unexpected '}' in a
    // pattern.`), the block never closed, and `Y` was swallowed into it.
    [InlineData("M = { F(a, }) = 1\nY = 2\nY")]
    [InlineData("M = { true(}) = 1\nY = 2\nY")]
    [InlineData("M = { F(~}) = 1\nY = 2\nY")]
    [InlineData("L = [F(a, ]) = 1]\nY = 2\nY")]
    [InlineData("G({ F(x }) = 1\nY = 2\nY")]
    public void ClauseHeadRecovery_NeverTakesAnEnclosingConstructsCloser(string source)
    {
        var parsed = Parser.ParseSyntax(source);
        Assert.True(parsed.HasErrors);
        Assert.Equal(2, Assert.Single(RootProperty(parsed.Root, "Y").DeclarationSpans).Start.Line);
        Assert.Equal("Y", Assert.IsType<Expr.Resolve>(parsed.Root.Output[^1]).Name);
    }

    // ── A declaration head is never an operand ──────────────────────────────

    public static TheoryData<string, string, int, int> DanglingContinuationCases()
    {
        var data = new TheoryData<string, string, int, int>();
        // first line (ending in a token that demands more), the dangling token's columns
        (string Line, int Start, int End)[] dangling =
        [
            ("1 +", 3, 4), ("1 -", 3, 4), ("1 /", 3, 4), ("1 div", 3, 6), ("2 ^", 3, 4),
            ("1 <", 3, 4), ("1 ==", 3, 5), ("true and", 6, 9), ("true or", 6, 8),
            ("1,", 2, 3), ("-", 1, 2), ("not", 1, 4), ("A =", 3, 4), ("A = 1 +", 7, 8),
            ("Pair = (1, 2)\nPair:", 5, 6), ("F(x) =", 6, 7), ("p, q =", 6, 7),
        ];
        (string Declaration, string Name)[] declarations =
        [
            ("Good = 41", "Good"), ("public Good = 41", "Good"), ("Good(x) = x", "Good"),
            ("Good, Other = 1, 2", "Good"), ("*Good = 1, 2", "Good"),
        ];
        foreach (var (line, start, end) in dangling)
        {
            foreach (var (declaration, name) in declarations)
                data.Add(line + "\n" + declaration, name, start, end);
        }

        return data;
    }

    [Theory]
    [MemberData(nameof(DanglingContinuationCases))]
    public void DanglingContinuation_NeverTakesTheNextLinesDeclarationHead(string source, string declared, int start, int end)
    {
        // Before #9 the next line's name became the operand, the declaration was lost,
        // and its '=' was reported as a head "assembled across a physical newline".
        var parsed = Parser.ParseSyntax(source);
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticCode.UnexpectedToken, diagnostic.Code);
        var danglingLine = source.Count(c => c == '\n');
        Assert.Equal(new SourceSpan(danglingLine, start, danglingLine, end), diagnostic.Span);
        Assert.Contains("The next line begins a declaration, which never continues an expression.", diagnostic.Message, StringComparison.Ordinal);
        var property = RootProperty(parsed.Root, declared);
        Assert.Equal(danglingLine + 1, property.DeclarationSpans[0].Start.Line);
        Assert.Equal(source.Contains("public Good", StringComparison.Ordinal), property.IsPublic);
    }

    [Fact]
    public void TrailingDot_NeverTakesTheNextLinesDeclarationHeadAsItsMember()
    {
        var parsed = Parser.ParseSyntax("A = { B = 1 }\nX = A.\nGood = 2\nGood");
        Assert.Equal(
            new[] { "[UnexpectedToken] 2:6-2:7 Expected property name after '.'. The next line begins a declaration, which never continues an expression." },
            parsed.Diagnostics.Select(Describe));
        Assert.Equal(new[] { "A", "X", "Good" }, parsed.Root.Properties.Select(p => p.Name));
    }

    [Theory]
    [InlineData("1 +\n2", "3")]
    [InlineData("A = 1 +\n2\nA", "3")]
    [InlineData("A =\n5\nA", "5")]
    [InlineData("1,\n2", "1\n2")]
    [InlineData("-\n3", "-3")]
    [InlineData("not\ntrue", "false")]
    [InlineData("Pair = (1, 2)\nX = Pair:\n0\nX", "1")]
    [InlineData("A = { B = 3 }\nX = A.\nB\nX", "3")]
    [InlineData("A = 2\nB = 3\nA*\nB", "6")]
    public void IncompleteLine_StillContinuesIntoAnExpressionOnTheNextLine(string source, string expected)
    {
        Assert.False(Parser.Parse(source).HasErrors, source);
        var result = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));
        Assert.Equal(expected, result.ToDisplayString().Replace("\r\n", "\n"));
    }

    // ── Clause heads confine their recovery ─────────────────────────────────

    [Theory]
    [InlineData("F([a, b]) = a + b\nNext = 1\nNext", "[UnexpectedToken] 1:3-1:4 Unexpected '[' in a pattern.")]
    [InlineData("F({a}) = a\nNext = 1\nNext", "[UnexpectedToken] 1:3-1:4 Unexpected '{' in a pattern.")]
    [InlineData("F() = 1\nNext = 1\nNext", "[UnexpectedToken] 1:3-1:4 Unexpected ')' in a pattern.")]
    [InlineData("F(x +) = x\nNext = 1\nNext", "[UnexpectedToken] 1:5-1:6 Expected ')' but found '+'.")]
    [InlineData("F(1 + 2) = 3\nNext = 1\nNext", "[UnexpectedToken] 1:5-1:6 Expected ')' but found '+'.")]
    [InlineData("F(a.b) = 3\nNext = 1\nNext", "[UnexpectedToken] 1:4-1:5 Expected ')' but found '.'.")]
    [InlineData("F(a\nb) = a + b\nNext = 1\nNext", "[UnexpectedToken] 2:1-2:2 Expected ')' but found a name.")]
    [InlineData("F(~) = 1\nNext = 1\nNext", "[InvalidGraceMarker] 1:3-1:4 Grace is not allowed in clause-head patterns.")]
    public void MalformedClauseHead_ReportsOnce_AndKeepsItsBodyInsideTheClause(string source, string diagnostic)
    {
        // Before #9 these cascaded into 2-8 diagnostics ("Expected '=' …", stray ')',
        // stray '=') and leaked the clause body to the enclosing scope as output rows.
        var parsed = Parser.ParseSyntax(source);
        Assert.Equal(new[] { diagnostic }, parsed.Diagnostics.Select(Describe));
        Assert.Equal(new[] { "F", "Next" }, parsed.Root.Properties.Select(p => p.Name).Order(StringComparer.Ordinal));
        Assert.Equal("Next", Assert.IsType<Expr.Resolve>(Assert.Single(parsed.Root.Output)).Name);
        var f = RootProperty(parsed.Root, "F").Value;
        Assert.NotEmpty(f is Algorithm.Conditional conditional ? Assert.Single(conditional.Branches).Body.Output : f.Output);
    }

    [Fact]
    public void ReservedLiteralHead_SkipsExactlyTheHead()
    {
        // The skip used to stop at the FIRST '=' — inside the parentheses.
        var parsed = Parser.ParseSyntax("false(x = 1) = 2\nNext = 1\nNext");
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.Equal(new SourceSpan(1, 1, 1, 6), diagnostic.Span);
        Assert.Equal(new[] { "Next" }, parsed.Root.Properties.Select(p => p.Name));
        Assert.Equal(2, Assert.IsType<Expr.Num>(parsed.Root.Output[0]).Value);
    }

    [Theory]
    // A recovered head keeps its clause in the family but takes part in no cross-clause
    // check: before #9 `F(x +) = x` poisoned the valid `F(y) = y` with a duplicate-pattern
    // error, and `F(-x) = x` (recovered as two binders) with a branch-arity mismatch.
    [InlineData("F(x +) = x\nF(y) = y\nF(1)", 2)]
    [InlineData("F(-x) = x\nF(0) = 0\nF(1)", 2)]
    [InlineData("F(0) = 0\nF(x +) = x\nF(y) = y\nF(1)", 3)]
    public void RecoveredClauseHead_DoesNotPoisonItsFamily(string source, int clauses)
    {
        var parsed = Parser.ParseSyntax(source);
        var diagnostic = Assert.Single(parsed.Diagnostics);
        Assert.Equal(DiagnosticCode.UnexpectedToken, diagnostic.Code);
        Assert.Equal(clauses, Assert.IsType<Algorithm.Conditional>(RootProperty(parsed.Root, "F").Value).Branches.Count);
    }

    [Fact]
    public void CleanClauseHeads_StillReportFamilyInconsistencies()
    {
        Assert.Equal(
            new[] { "[DuplicateBranchPattern] 2:1-2:9 Duplicate branch pattern for conditional algorithm 'F'." },
            Parser.ParseSyntax("F(0) = 0\nF(0) = 1\nF(0)").Diagnostics.Select(Describe));
        // A recovered FIRST clause moves the reference to the first clean one.
        var arity = Assert.Single(Parser.ParseSyntax("F(x +) = x\nF(0) = 0\nF(a, b) = a\nF(1)").Diagnostics,
            d => d.Code == DiagnosticCode.BranchArityMismatch);
        Assert.Contains("Expected 1 (from branch 2), but branch 3 has arity 2.", arity.Message, StringComparison.Ordinal);
    }

    // ── Recovery shapes are shapes a valid program can have ─────────────────

    [Theory]
    [InlineData("F(*a, *b) = a\nF(1)")]
    [InlineData("F((*a, *b)) = a\nF((1, 2))")]
    [InlineData("F(*a, (*b, *c)) = a\nF(1)")]
    [InlineData("F(*a, *a) = a\nF(1)")]
    [InlineData("public F(*a, *b, *c) = a\nF(1)")]
    [InlineData("M = { F(*a, *b) = a }\nM.F(1)")]
    [InlineData("(F(*a, *b) = a)")]
    [InlineData("*a, *b = 1, 2\na, b")]
    public void SeveralCollectingBindingsAtOneLevel_RecoverToOneCollector_AndEditorToolingAcceptsIt(string source)
    {
        // The recovered tree used to keep every collector, a parameter shape no valid
        // program can have; SemanticModelBuilder.Build then threw from the binding planner.
        var parsed = SourceProvenance.ParseAllowingDiagnostics(source);
        Assert.Contains(parsed.Diagnostics, d => d.Code == DiagnosticCode.InvalidCollectingBinding);
        var model = SemanticModelBuilder.Build(parsed.Parsed);
        Assert.NotEmpty(model.Declarations);

        foreach (var algorithm in AllUserAlgorithms(parsed.Root))
            Assert.False(ParameterPattern.HasMultipleCollectingCapturesAtAnyLevel(algorithm.ParameterPatterns), source);
    }

    [Fact]
    public void CollectorInALiteralHead_IsReportedOnce()
    {
        var parsed = Parser.ParseSyntax("F(0, *a) = a\nF(0)");
        Assert.Equal(
            new[] { "[InvalidCollectingBinding] 1:1-1:13 Collecting bindings are only supported in ordinary explicit parameter lists for 'F'." },
            parsed.Diagnostics.Select(Describe));
    }

    private static IEnumerable<Algorithm.User> AllUserAlgorithms(Algorithm root)
    {
        var pending = new Stack<Algorithm>();
        pending.Push(root);
        while (pending.Count > 0)
        {
            var algorithm = pending.Pop();
            if (algorithm is Algorithm.User user)
            {
                yield return user;
                foreach (var property in user.Properties)
                    pending.Push(property.Value);
                foreach (var row in user.Output)
                {
                    if (row is Expr.AlgorithmExpr nested)
                        pending.Push(nested.Algorithm);
                    if (row is Expr.Call { Function: Expr.AlgorithmExpr helper })
                        pending.Push(helper.Algorithm);
                }
            }
            else if (algorithm is Algorithm.Conditional conditional)
            {
                foreach (var branch in conditional.Branches)
                    pending.Push(branch.Body);
            }
        }
    }

    // ── Characters the lexer reported are invisible to the grammar ──────────

    [Theory]
    [InlineData("A = true\nX = !A\nX", "[UnexpectedCharacter] 2:5-2:6 Unexpected character: '!'. Use 'not' for logical negation.")]
    [InlineData("P = 1 @ 2\nQ = 3\nP, Q", "[UnexpectedCharacter] 1:7-1:8 Unexpected character: '@'.")]
    [InlineData("A = 1 + @ 2\nA", "[UnexpectedCharacter] 1:9-1:10 Unexpected character: '@'.")]
    [InlineData("F(a @, b) = a\nF(1, 2)", "[UnexpectedCharacter] 1:5-1:6 Unexpected character: '@'.")]
    [InlineData("A = @\nGood = 2\nGood", "[UnexpectedCharacter] 1:5-1:6 Unexpected character: '@'.")]
    public void LexerReportedCharacter_IsReportedOnce(string source, string diagnostic)
    {
        var parsed = Parser.ParseSyntax(source);
        Assert.Equal(new[] { diagnostic }, parsed.Diagnostics.Select(Describe));
    }

    [Fact]
    public void LexerReportedCharacter_InsideADefinitionBody_KeepsTheRestOfTheLineInTheBody()
    {
        // `2` used to end the line-bounded body at the '@' and leak to the root output.
        var parsed = Parser.ParseSyntax("P = 1 @ 2\nQ = 3\nP, Q");
        Assert.Equal(2, RootProperty(parsed.Root, "P").Value.Output.Count);
        Assert.Equal(2, parsed.Root.Output.Count);
    }

    // The grammar skips a reported character exactly like a comment: every decision —
    // continuation, slot boundary, declaration lookahead — is made as if it were not there.
    // Each of these used to cost a second diagnostic, and most lost structure besides (`A @= 1`
    // declared nothing, `F@(x) = x` lost its clause, `open @Math` its target, `1@ + 2` split
    // into three rows, `[1` newline `@ 2]` moved `2` out of the list).
    [Theory]
    [InlineData("1@ + 2")]
    [InlineData("A = { B = 1 }\nA@.B")]
    [InlineData("F(x) = x\nF@(1)")]
    [InlineData("A = (1, 2)\nA@:0")]
    [InlineData("A @= 1\nA")]
    [InlineData("A =@ 1\nA")]
    [InlineData("F@(x) = x\nF(1)")]
    [InlineData("F(@x) = x\nF(1)")]
    [InlineData("F(x)@ = x\nF(1)")]
    [InlineData("public @A = 1\nA")]
    [InlineData("x, @y = 1, 2\nx + y")]
    [InlineData("open @Math\nPi")]
    [InlineData("open Math, @M\nM = { public V = 1 }\nV + Pi")]
    [InlineData("A = { B = 1 }\nA.@B")]
    [InlineData("A = true\nX = !A\nX")]
    [InlineData("[1\n@ 2]")]
    [InlineData("[1\n@]")]
    [InlineData("X = 1 +\n@\n2\nX")]
    public void ReportedCharacter_IsInvisibleToTheGrammar(string source)
    {
        var parsed = Parser.Parse(source);
        Assert.Equal(DiagnosticCode.UnexpectedCharacter, Assert.Single(parsed.Diagnostics).Code);

        var withoutIt = Parser.Parse(DeleteReportedCharacters(source));
        Assert.Empty(withoutIt.Diagnostics);
        Assert.Equal(LeanAstEncoder.EncodeProgram(withoutIt.Root), LeanAstEncoder.EncodeProgram(parsed.Root));
    }

    // Where the grammar needs a piece exactly where a reported character stands — an operand
    // before a closer, a comma, the end of input, or an operator; a member name; an open
    // target; a pattern item; the comma between two items — the character IS that piece:
    // filled without a second report. A clause head that needed such a fill is a recovered
    // head, so it poisons no family check (`F(@) = 1` beside `F(x) = x`).
    [Theory]
    [InlineData("(1 + @)")]
    [InlineData("F(x, y) = x\nF(1, @)")]
    [InlineData("F(x) = x\nF(1,\n@)")]
    [InlineData("[1, @]")]
    [InlineData("1, @, 2")]
    [InlineData("[\n1,\n@,\n2\n]")]
    [InlineData("1 < @ < 2")]
    [InlineData("1 + @ * 2")]
    [InlineData("if(@, 1, 2)")]
    [InlineData("-@")]
    [InlineData("A = @\nB = 1\nB")]
    [InlineData("X = 1 +\n@\nGood = 2\nGood")]
    [InlineData("A = { B = 1 }\nA.@")]
    [InlineData("open @")]
    [InlineData("open M, @\nM = { public V = 1 }")]
    [InlineData("open Math @Pi")]
    [InlineData("P = 1 @ 2\nP")]
    [InlineData("F(x, @) = x\nF(1, 2)")]
    [InlineData("F(@) = 1\nF(x) = x\nF(2)")]
    [InlineData("F(x @ y) = x\nF(1, 2)")]
    public void ReportedCharacter_StandsInTheMissingPiece_WithoutASecondReport(string source)
    {
        var diagnostic = Assert.Single(Parser.ParseSyntax(source).Diagnostics);
        Assert.Equal(DiagnosticCode.UnexpectedCharacter, diagnostic.Code);
    }

    // Structure is never filled, and a piece is filled only where the character stands: a
    // construct still missing its closer after a reported character is its own error, and an
    // open target belongs on the `open` line, so a character on the next line stands in for
    // nothing there.
    [Theory]
    [InlineData("(1 @", DiagnosticCode.UnexpectedToken, "Expected ')' but found end of input.")]
    [InlineData("[1, 2 @", DiagnosticCode.UnexpectedToken, "Expected ']' but found end of input.")]
    [InlineData("F(x) = x\nF(1 @", DiagnosticCode.UnexpectedToken, "Expected ')' but found end of input.")]
    [InlineData("open\n@ Math", DiagnosticCode.InvalidOpenTargetList, "Expected an open target after 'open' on the same physical line.")]
    public void ReportedCharacter_NeverStandsInStructure_OrAwayFromItsPosition(string source, DiagnosticCode code, string message)
    {
        var diagnostics = Parser.ParseSyntax(source).Diagnostics;
        Assert.Equal(2, diagnostics.Count);
        Assert.Contains(diagnostics, d => d.Code == DiagnosticCode.UnexpectedCharacter);
        Assert.Contains(diagnostics, d => d.Code == code && d.Message == message);
    }

    /// <summary>
    /// The law over every tutorial program the front end accepts (and the Lean encoding
    /// covers): one reported character written at any token boundary adds the lexer's
    /// diagnostic and changes nothing else — no other diagnostic, and the same elaborated
    /// program. Excluded are the boundaries next to a `*` or `~` marker, whose attachment is
    /// exact source adjacency (a character between a marker and its operand detaches it), and
    /// the end of a comment, which the character would join.
    /// </summary>
    [Fact]
    public void ReportedCharacter_AtAnyTokenBoundaryOfAValidProgram_AddsOnlyTheLexerReport()
    {
        var programs = 0;
        var insertions = 0;
        foreach (var example in TutorialCorpus.Examples)
        {
            var source = example.Source;
            var clean = Parser.Parse(source);
            if (clean.HasErrors)
                continue;

            string expected;
            try
            {
                expected = LeanAstEncoder.EncodeProgram(clean.Root);
            }
            catch (NotSupportedException)
            {
                continue; // decimals and the like are outside the Lean encoding
            }

            programs++;
            var tokens = Lexer.Tokenize(source).Tokens;
            var cleanDiagnostics = clean.Diagnostics.Select(d => (d.Code, d.Message)).ToList();
            foreach (var point in TokenBoundaries(source, tokens))
            {
                var variant = source.Insert(point, "@");
                var parsed = Parser.Parse(variant);
                var context = $"tutorial.md fence at line {example.FenceLine}, '@' at offset {point}: {variant.Replace("\n", "\\n", StringComparison.Ordinal)}";
                Assert.True(parsed.Diagnostics.Count(d => d.Code == DiagnosticCode.UnexpectedCharacter) == 1, context);
                Assert.True(
                    cleanDiagnostics.SequenceEqual(parsed.Diagnostics
                        .Where(d => d.Code != DiagnosticCode.UnexpectedCharacter)
                        .Select(d => (d.Code, d.Message))),
                    context);
                Assert.True(expected == LeanAstEncoder.EncodeProgram(parsed.Root), context);
                insertions++;
            }
        }

        // A floor against vacuity (measured September 2026: 255 programs, 8,479 insertions).
        Assert.True(programs >= 240 && insertions >= 8000, $"Only {programs} programs and {insertions} insertions were checked.");

        static IEnumerable<int> TokenBoundaries(string source, IReadOnlyList<Token> tokens)
        {
            var points = new SortedSet<int> { 0, source.Length };
            foreach (var token in tokens)
            {
                points.Add(token.Position);
                points.Add(token.Position + token.Length);
            }

            foreach (var point in points)
            {
                if (tokens.Any(t => t.Position < point && point < t.Position + t.Length))
                    continue; // inside a token
                if (tokens.Any(t => t.Kind is TokenKind.Star or TokenKind.Tilde && (t.Position == point || t.Position + t.Length == point)))
                    continue; // marker attachment is exact source adjacency
                if (tokens.Any(t => t.Kind == TokenKind.Comment && t.Position + t.Length == point))
                    continue; // the character would join the comment
                yield return point;
            }
        }
    }

    private static string DeleteReportedCharacters(string source)
    {
        var text = new System.Text.StringBuilder(source);
        foreach (var token in Lexer.Tokenize(source).Tokens.Where(t => t.Kind == TokenKind.Bad).OrderByDescending(t => t.Position))
            text.Remove(token.Position, token.Length);
        return text.ToString();
    }

    // ── Diagnostics name the actual cause, at a position ────────────────────

    [Theory]
    [InlineData("A = x = 1", false)]
    [InlineData("[A = 1]", false)]
    [InlineData("x, y, = 1, 2", false)]
    [InlineData("A\n= 1", true)]
    [InlineData("Foo\n(x) = x + 1", true)]
    [InlineData("x, y\n= 1, 2", true)]
    public void StrayEquals_ExplainsTheSplitHeadOnlyWhenANewlineSplitOne(string source, bool splitHead)
    {
        var equals = Assert.Single(Parser.ParseSyntax(source).Diagnostics, d => d.Message.StartsWith("Unexpected '='.", StringComparison.Ordinal));
        Assert.Equal(splitHead, equals.Message.Contains("A declaration head cannot be assembled across a physical newline", StringComparison.Ordinal));
        Assert.Equal(!splitHead, equals.Message.Contains("To compare values, use '=='.", StringComparison.Ordinal));
    }

    [Theory]
    [InlineData("F() = {", 1, 1, 1, 2)]      // only the spanless recovery binder: the clause name
    [InlineData("F(,x) = { }", 1, 4, 1, 5)]  // the first WRITTEN parameter
    [InlineData("F(x) = { }", 1, 3, 1, 4)]
    public void ExplicitParametersWithoutOutput_IsAlwaysPositioned(string source, int line, int column, int endLine, int endColumn)
    {
        var diagnostic = Assert.Single(Parser.ParseSyntax(source).Diagnostics, d => d.Code == DiagnosticCode.ExplicitParametersRequireOutput);
        Assert.Equal(new SourceSpan(line, column, endLine, endColumn), diagnostic.Span);
    }

    // ── Termination and the swallowed-suffix law over generated sources ────

    /// <summary>
    /// Every string of up to four tokens over an alphabet of delimiters, declaration-head
    /// starters (`=`, `public`, `true`, `F(`), continuation tokens, newlines, and a character
    /// the lexer reports parses to completion (a non-consuming recovery return must be
    /// matched by every loop that could re-admit its token: the first #9 operand rule refused
    /// a reserved-literal head that the slot boundary kept admitting, and `A` newline `true=`
    /// hung), with a linear diagnostic count and no parser diagnostic that names the reported
    /// character; and whenever such a malformed source's delimiters balance by count, a
    /// declaration appended on a new line stays a root declaration.
    /// </summary>
    [Fact]
    public async Task GeneratedMalformedSources_Terminate_AndNeverSwallowALaterDeclaration()
    {
        string[] alphabet = ["(", ")", "[", "]", "{", "}", ",", "x", "=", "+", ".", "\n", "true ", "public ", "F(", "@"];
        var current = "";
        var parsed = 0;
        var sweep = Task.Run(() =>
        {
            var indices = new int[4];
            for (var length = 1; length <= 4; length++)
            {
                Array.Clear(indices);
                while (true)
                {
                    var source = string.Concat(indices.Take(length).Select(i => alphabet[i]));
                    Volatile.Write(ref current, source);
                    var result = Parser.ParseSyntax(source);
                    Assert.True(result.Diagnostics.Count <= 2 * source.Length + 1, $"{result.Diagnostics.Count} diagnostics: {Escape(source)}");
                    Assert.False(
                        result.Diagnostics.Any(d => d.Message.Contains("unrecognized character", StringComparison.Ordinal)),
                        $"The parser named a character the lexer already reported: {Escape(source)}");
                    if (result.HasErrors && DelimitersBalanceByCount(source))
                    {
                        var withSuffix = Parser.ParseSyntax(source + "\nGood = 41\nGood");
                        var good = Assert.Single(withSuffix.Root.Properties, p => p.Name == "Good");
                        Assert.True(
                            Assert.Single(good.DeclarationSpans).Start.Line == source.Count(c => c == '\n') + 2,
                            $"The appended declaration was swallowed after: {Escape(source)}");
                    }

                    parsed++;
                    var position = 0;
                    while (position < length && ++indices[position] == alphabet.Length)
                        indices[position++] = 0;
                    if (position == length)
                        break;
                }
            }
        });

        var finished = await Task.WhenAny(sweep, Task.Delay(TimeSpan.FromMinutes(2)));
        Assert.True(finished == sweep, $"The sweep did not terminate; last input: {Escape(Volatile.Read(ref current))}");
        await sweep;
        Assert.Equal(16 + 256 + 4096 + 65536, parsed);

        static string Escape(string source) => source.Replace("\n", "\\n", StringComparison.Ordinal);

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
    public async Task DeclarationHeadAfterASlotBoundary_Terminates_WithOneTargetedDiagnostic()
    {
        // The reserved-literal and public heads are part of THE declaration-starter
        // relation: the slot boundary stops before them exactly where operand recovery
        // refuses them, so the loop cannot re-admit the refused token (the first version
        // of the operand rule looped forever on `A` newline `true=`). Guarded, so a
        // regression fails instead of hanging the suite.
        var parses = Task.Run(() => (
            Reserved: Parser.ParseSyntax("A\ntrue = 1"),
            ReservedInList: Parser.ParseSyntax("1;\nfalse(x) = x\n[1,\ntrue = 2]"),
            Public: Parser.ParseSyntax("A\npublic B = 1\nB")));
        Assert.True(await Task.WhenAny(parses, Task.Delay(TimeSpan.FromMinutes(1))) == parses, "The parse did not terminate.");
        var (reserved, reservedInList, publicHead) = await parses;

        Assert.Contains("reserved Boolean literal", Assert.Single(reserved.Diagnostics).Message, StringComparison.Ordinal);
        Assert.Contains(reservedInList.Diagnostics, d => d.Message.Contains("reserved Boolean literal", StringComparison.Ordinal));
        Assert.Empty(publicHead.Diagnostics);
        Assert.True(RootProperty(publicHead.Root, "B").IsPublic);
    }

    // ── Invalid source never evaluates; editor tooling accepts every recovery tree ──

    public static TheoryData<string> RecoveryShapes() => new()
    {
        "(Probe(), 2]\nX = Probe()\nX",
        "X = F((Probe(), 2], 3)\nF(a, b) = a\nX",
        "X = Probe() +\nGood = Probe()\nGood",
        "F([a]) = Probe()\nF(1)",
        "F(x +) = Probe()\nF(y) = y\nF(1)",
        "F(*a, *b) = Probe()\nF(1)",
        "X = !Probe()\nX",
        // The grammar sees a complete program here, so the lexer's report alone must gate it.
        "A @= Probe()\nA",
        "X = Probe() @\nX",
        "]\nX = Probe()\nX",
        "M = { F(a, }) = Probe()\nY = Probe()\nY",
    };

    [Theory]
    [MemberData(nameof(RecoveryShapes))]
    public async Task RecoveryTree_NeverEvaluates_AndTheSemanticModelAcceptsIt(string source)
    {
        var calls = 0;
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(HostOperation.Create("Probe", (_, _) =>
            {
                calls++;
                return new Result.Atom(1);
            })),
        };

        Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source, options));
        Assert.IsType<RunResult.ParseFailure>(await KatLangEngine.RunAsync(source, options));
        Assert.Equal(0, calls);

        var parsed = Parser.Parse(source, options);
        Assert.True(parsed.HasErrors);
        var model = SemanticModelBuilder.Build(parsed);
        foreach (var occurrence in model.IdentifierOccurrences)
        {
            _ = model.FindResolutionAt(occurrence.Span.Start);
            _ = model.GetVisibleSymbolsAt(occurrence.Span.Start);
            _ = model.FindPropertyAt(occurrence.Span.Start);
        }
    }
}
