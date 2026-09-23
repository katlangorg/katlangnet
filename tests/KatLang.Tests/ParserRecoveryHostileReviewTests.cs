using KatLang.Semantics;
using KatLang.ParserFuzz;

namespace KatLang.Tests;

public class ParserRecoveryHostileReviewTests
{
    [Fact]
    public void RecoveredHeadMetadata_PreservesCoreEqualityAndSurvivesElaboration()
    {
        const string source = "F(x +) = x\nF(a, b) = a";
        var syntax = Parser.ParseSyntax(source);
        Assert.True(syntax.HasErrors);
        var elaborated = SourceProvenance.ParseAllowingDiagnostics(source);
        foreach (var root in new[] { syntax.Root, elaborated.Root })
        {
            var family = Assert.IsType<Algorithm.Conditional>(Assert.Single(root.Properties).Value);
            Assert.True(family.Branches[0].HasRecoveredHead);
            Assert.False(family.Branches[1].HasRecoveredHead);
            var cleanView = family.Branches[0] with { HasRecoveredHead = false };
            Assert.Equal(family.Branches[0], cleanView);
            Assert.Equal(family.Branches[0].GetHashCode(), cleanView.GetHashCode());
        }
    }

    [Theory]
    [InlineData("F(", "]", ")")]
    [InlineData("F(", "}", ")")]
    [InlineData("public F(", "]", ")")]
    [InlineData("true(", "]", ")")]
    [InlineData("F([", ")]", "])")]
    [InlineData("F({", "]}", "})")]
    public void HeadLookahead_CannotCrossARegionAlreadyClosedByMismatches(string head, string close, string tail)
    {
        var source = $"{head}{close}\nGood = 41\n{tail} = 1\nGood + 1";
        var parsed = Parser.ParseSyntax(source);
        Assert.True(parsed.HasErrors);
        var good = Assert.Single(parsed.Root.Properties, p => p.Name == "Good");
        Assert.Equal(new SourceSpan(2, 1, 2, 5), Assert.Single(good.DeclarationSpans));
        CheckEditor(source);
    }

    [Theory]
    [InlineData("F(x @ y) = x")]
    [InlineData("F((x @ y)) = x")]
    [InlineData("F(١) = 0")]
    [InlineData("F(1e99999) = 0")]
    [InlineData("F('oops\n) = 0")]
    public void LexicallyRecoveredHead_CannotPoisonCleanFamilyChecks(string head)
    {
        var source = head + "\nF(a) = a\nF(b, c) = b";
        var parsed = Parser.ParseSyntax(source);
        Assert.DoesNotContain(parsed.Diagnostics, d => d.Code == DiagnosticCode.DuplicateBranchPattern);
        var mismatch = Assert.Single(parsed.Diagnostics, d => d.Code == DiagnosticCode.BranchArityMismatch);
        Assert.Contains("Expected 1 (from branch 2), but branch 3 has arity 2.", mismatch.Message);
        CheckEditor(source);
    }

    [Theory]
    [InlineData("A.@ 1")]
    [InlineData("F(A.@ 1)")]
    [InlineData("[A.@ 1]")]
    [InlineData("P = A.@ 1")]
    public void ReportedCharacter_CannotFillBothMemberAndSeparator(string source)
    {
        var parsed = Parser.ParseSyntax(source);
        Assert.Single(parsed.Diagnostics, d => d.Code == DiagnosticCode.UnexpectedCharacter);
        Assert.Single(parsed.Diagnostics, d => d.Code == DiagnosticCode.UnseparatedSameLineItem);
        Assert.Equal(2, parsed.Diagnostics.Count);
    }

    [Theory]
    [InlineData("public Good = 41")]
    [InlineData("open Math")]
    [InlineData("true = 41")]
    [InlineData("~Good = 41")]
    [InlineData("*Good = 41")]
    public void DanglingDot_BlamesTheDotBeforeEveryDeclarationKind(string declaration)
    {
        var parsed = Parser.ParseSyntax("A.\n" + declaration);
        var diagnostic = Assert.Single(parsed.Diagnostics, d => d.Message.StartsWith("Expected property name", StringComparison.Ordinal));
        Assert.Equal(new SourceSpan(1, 2, 1, 3), diagnostic.Span);
    }

    [Theory]
    [InlineData("F(x, @) = { _error_ = 1\nx + _error_ }")]
    [InlineData("F(@, @) = { _error_ = 1\n_error_ }")]
    [InlineData("F(0, @) = { _error_ = 1\n_error_ }\nF(x,y)=x")]
    public void PlaceholderBinding_CannotCaptureOrCollideWithAUserSpelling(string source)
    {
        var parsed = Parser.Parse(source);
        Assert.True(parsed.HasErrors);
        Assert.DoesNotContain(parsed.Diagnostics, d => d.Code == DiagnosticCode.ParameterPropertyCollision);
        var model = SemanticModelBuilder.Build(parsed);
        var declaration = Assert.Single(model.FindDeclarations("_error_"));
        var reference = model.IdentifierResolutions.Last(r => r.Occurrence.Name == "_error_");
        Assert.Equal(declaration, reference.ResolvedDeclaration);
        Assert.DoesNotContain(model.ScopeVisibilities.SelectMany(s => s.Symbols), s => !Lexer.IsValidIdentifier(s.Name));
    }

    [Theory]
    [InlineData("@\npublic Export = 99")]
    [InlineData("F(x +)=x\npublic Export = 99")]
    [InlineData("[1)\npublic Export = 99")]
    public async Task InvalidModule_PreventsEvaluationOfTheCaller(string module)
    {
        var calls = 0;
        var options = new RunOptions
        {
            DownloadCode = (_, _) => ValueTask.FromResult(module),
            HostOperations = HostOperations.Create(HostOperation.Create("Probe", (_, _) =>
            {
                calls++;
                return new Result.Atom(1);
            })),
        };
        const string source = "M = load('https://katlang.org/invalid.kat')\nProbe()";
        var failure = Assert.IsType<RunResult.ParseFailure>(await KatLangEngine.RunAsync(source, options));
        Assert.Contains(failure.Errors, e => e.Code == KatLangErrorCode.InvalidLoadedSource);
        Assert.Equal(0, calls);
        var parsed = await Parser.ParseAsync(source, options);
        var model = SemanticModelBuilder.Build(parsed);
        Assert.Empty(model.FindDeclarations("Export"));
    }

    [Fact]
    public void WrongCloserMatrix_PreservesTheSuffixAtDepthsOneThroughFive()
    {
        (string Open, string Close)[] forms = [("(", ")"), ("[", "]"), ("{", "}"), ("F(", ")")];
        var cases = 0;
        for (var depth = 1; depth <= 5; depth++)
        foreach (var outer in forms)
        foreach (var inner in forms)
        foreach (var wrong in new[] { ")", "]", "}" }.Where(c => c != inner.Close))
        {
            var damaged = string.Concat(Enumerable.Repeat(outer.Open, depth - 1))
                + inner.Open + "1, @" + wrong
                + string.Concat(Enumerable.Repeat(outer.Close, depth - 1));
            var source = damaged + "\nGood = 41\nGood + 1";
            var parsed = Parser.ParseSyntax(source);
            Assert.True(parsed.HasErrors, source);
            Assert.Single(parsed.Root.Properties, p => p.Name == "Good");
            Assert.IsType<Expr.Binary>(parsed.Root.Output[^1]);
            CheckEditor(source);
            cases++;
        }
        Assert.Equal(160, cases);
    }

    [Fact]
    public void CombinedClauseCorruption_PreservesOwnershipAndEditorSafety()
    {
        string[] heads = ["F((a, @])", "F([a, @})", "F({@bad })", "F((a, [b, @}]))",
            "F(*a, @ *b, *c)", "F((*a, @ *b, *c))", "F(0, *a, @ *b)"];
        foreach (var head in heads)
        {
            var source = "Root = {\n" + head + " = 1 +\nGood = 41\nGood\n}\nTail = 42\nTail";
            var raw = Parser.ParseSyntax(source);
            Assert.True(raw.HasErrors, source);
            Assert.Single(raw.Root.Properties, p => p.Name == "Tail");
            FrontEndInvariants.Check(source);
            CheckEditor(source);
        }
    }

    [Fact]
    public void DifferentBadCodeUnits_PreserveTokensDiagnosticsAndTheValidProgram()
    {
        string[] badTokens = ["@", "$", "\\", "\u2603", "\U0001F600", "\uD800", "\uDC00", "\u200B"];
        string[] templates = ["1{0}+2", "1+{0}2", "1< {0}2 <= 3", "{0}A=1\nA", "public{0} A=1\nA",
            "F({0}x)=x\nF(1)", "A='😀'\nA{0}.string", "[1,{0}2]", "(1,{0}2)",
            "A={{B=1}}\nA.{0}B", "1{0}# comment\n+2", "1 # comment\n{0}+2"];
        foreach (var bad in badTokens)
        foreach (var template in templates)
        foreach (var newline in new[] { "\n", "\r\n", "\r" })
        {
            var clean = string.Format(template, "").Replace("\n", newline);
            var source = string.Format(template, bad).Replace("\n", newline);
            var parsed = Parser.Parse(source);
            var lexical = Lexer.Tokenize(source);
            var badToken = Assert.Single(lexical.Tokens, t => t.Kind == TokenKind.Bad);
            Assert.Equal(bad.Length, badToken.Length);
            Assert.Equal(bad, source.Substring(badToken.Position, badToken.Length));
            var diagnostic = Assert.Single(parsed.Diagnostics, d => d.Code == DiagnosticCode.UnexpectedCharacter);
            Assert.Equal(badToken.Span, diagnostic.Span);
            var control = Parser.Parse(clean);
            Assert.Equal(control.Diagnostics.Select(d => d.Code), parsed.Diagnostics
                .Where(d => d.Code != DiagnosticCode.UnexpectedCharacter).Select(d => d.Code));
            Assert.Equal(LeanAstEncoder.EncodeProgram(control.Root), LeanAstEncoder.EncodeProgram(parsed.Root));
            Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source));
            FrontEndInvariants.Check(source);
        }
    }

    [Theory]
    [InlineData("'abc@def' # @ ! $ 😀")]
    [InlineData("'@'")]
    public void BadCharactersInsideStringsAndComments_AreOrdinaryContent(string source)
        => Assert.Empty(Parser.Parse(source).Diagnostics);

    [Theory]
    [InlineData("F(1 @ 2)")]
    [InlineData("F(1 @ @ 2)")]
    [InlineData("F(1 + @)")]
    [InlineData("F((1, @))")]
    [InlineData("F(x @ y) = x")]
    public void SingleHoleFill_StillNeedsOnlyLexicalReports(string source)
    {
        var parsed = Parser.ParseSyntax(source);
        Assert.NotEmpty(parsed.Diagnostics);
        Assert.All(parsed.Diagnostics, d => Assert.Equal(DiagnosticCode.UnexpectedCharacter, d.Code));
    }

    [Theory]
    [InlineData("F(0, *a, *b, *c) = a")]
    [InlineData("F((0, *a, *b), *c, *d) = a")]
    [InlineData("F(0, (*a, *b)) = a\nF(x) = x")]
    public void LiteralHeadRecovery_AlsoHasAtMostOneCollectorPerLevel(string source)
    {
        var parsed = Parser.ParseSyntax(source);
        Assert.True(parsed.HasErrors);
        var family = Assert.IsType<Algorithm.Conditional>(Assert.Single(parsed.Root.Properties).Value);
        foreach (var branch in family.Branches)
            CheckPattern(branch.Pattern);
        CheckEditor(source);

        static void CheckPattern(Pattern pattern)
        {
            if (pattern is not Pattern.SequenceValue group)
                return;
            Assert.True(group.Items.Count(p => p is Pattern.Bind { ParameterKind: ParameterKind.Collecting }) <= 1);
            foreach (var child in group.Items)
                CheckPattern(child);
        }
    }

    [Fact]
    public void LongMalformedRuns_HaveLinearDiagnosticsAndWork()
    {
        foreach (var unit in new[] { "]", "@", "@]", "1 " })
        {
            long previousSteps = 0;
            foreach (var length in new[] { 10_000, 20_000 })
            {
                var source = string.Concat(Enumerable.Repeat(unit, length)) + "\nGood=41\nGood";
                var observations = new ParserTraversalObservations();
                var parsed = Parser.ParseSyntaxObserved(source, observations);
                Assert.True(parsed.Diagnostics.Count <= 2 * length, unit);
                Assert.Single(parsed.Root.Properties, p => p.Name == "Good");
                Assert.True(observations.TokenSteps > 0);
                if (previousSteps > 0)
                    Assert.True(observations.TokenSteps <= 2.5 * previousSteps, $"{unit}: {previousSteps} -> {observations.TokenSteps}");
                previousSteps = observations.TokenSteps;
            }
        }
    }

    [Fact]
    public async Task ParseFailures_NeverEnterAnEvaluatorEvenWithCancelledEvaluation()
    {
        using var cancellation = new CancellationTokenSource();
        cancellation.Cancel();
        var options = new RunOptions { EvaluationCancellationToken = cancellation.Token, RandomSeed = 123 };
        string[] sources = ["F([a]) = random\nF(1)", "random +\nGood=41", "[random)",
            "F(*a,*b)=random\nF(1)", "random @", "F(x @ y)=random\nF(a)=a"];
        foreach (var source in sources)
        {
            Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run(source, options));
            Assert.IsType<RunResult.ParseFailure>(await KatLangEngine.RunAsync(source, options));
        }
        Assert.ThrowsAny<OperationCanceledException>(() => KatLangEngine.Run("random", options));
        await Assert.ThrowsAnyAsync<OperationCanceledException>(() => KatLangEngine.RunAsync("random", options));
    }

    private static void CheckEditor(string source)
    {
        var parsed = Parser.Parse(source);
        var model = SemanticModelBuilder.Build(parsed);
        foreach (var occurrence in model.IdentifierOccurrences)
        {
            _ = model.FindResolutionAt(occurrence.Span.Start);
            _ = model.GetVisibleSymbolsAt(occurrence.Span.Start);
            _ = model.FindPropertyAt(occurrence.Span.Start);
            _ = model.FindDeclarations(occurrence.Name);
        }
    }
}
