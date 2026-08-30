namespace KatLang.Tests;

/// <summary>
/// M5 structured diagnostic identity: every KatLang-produced front-end
/// <see cref="Diagnostic"/> carries a deliberate <see cref="DiagnosticCode"/>,
/// one code per semantic family, without any change to messages, severities,
/// or spans — and the <see cref="Diagnostic"/> record's compatibility and
/// identity contract around the added property is pinned deliberately.
/// </summary>
public class DiagnosticCodeTests
{
    // ── Record compatibility and identity contract ──────────────────────────

    [Fact]
    public void PositionalConstruction_StillWorks_AndCodeDefaultsToUnspecified()
    {
        // The pre-M5 positional constructor shape, exactly as external source
        // invokes it today.
        var diagnostic = new Diagnostic("boom", DiagnosticSeverity.Warning, new SourceSpan(1, 2, 3, 4));

        Assert.Equal("boom", diagnostic.Message);
        Assert.Equal(DiagnosticSeverity.Warning, diagnostic.Severity);
        Assert.Equal(new SourceSpan(1, 2, 3, 4), diagnostic.Span);
        Assert.Equal(DiagnosticCode.Unspecified, diagnostic.Code);
    }

    [Fact]
    public void Deconstruct_ShapeIsUnchanged_ThreePositionalComponents()
    {
        var diagnostic = new Diagnostic("boom", DiagnosticSeverity.Error, new SourceSpan(1, 2, 3, 4))
        {
            Code = DiagnosticCode.UnexpectedToken,
        };

        // Positional deconstruction stays three components; the code is not one
        // of them.
        var (message, severity, span) = diagnostic;
        Assert.Equal("boom", message);
        Assert.Equal(DiagnosticSeverity.Error, severity);
        Assert.Equal(new SourceSpan(1, 2, 3, 4), span);

        var deconstruct = typeof(Diagnostic).GetMethod(nameof(Diagnostic.Deconstruct));
        Assert.NotNull(deconstruct);
        Assert.Equal(3, deconstruct!.GetParameters().Length);
    }

    [Fact]
    public void WithCopy_PreservesTheCode()
    {
        var diagnostic = new Diagnostic("boom", DiagnosticSeverity.Error, new SourceSpan(1, 2, 3, 4))
        {
            Code = DiagnosticCode.DuplicateProperty,
        };

        var relocated = diagnostic with { Span = new SourceSpan(9, 9, 9, 9) };

        Assert.Equal(DiagnosticCode.DuplicateProperty, relocated.Code);
        Assert.Equal("boom", relocated.Message);
    }

    [Fact]
    public void Equality_IncludesTheCode_Deliberately()
    {
        // The code is semantic diagnostic identity, so it participates in value
        // equality and hashing: two diagnostics differing only in code are
        // different diagnostics.
        var span = new SourceSpan(1, 2, 3, 4);
        var coded = new Diagnostic("boom", DiagnosticSeverity.Error, span) { Code = DiagnosticCode.UnexpectedToken };
        var sameCoded = new Diagnostic("boom", DiagnosticSeverity.Error, span) { Code = DiagnosticCode.UnexpectedToken };
        var uncoded = new Diagnostic("boom", DiagnosticSeverity.Error, span);

        Assert.Equal(coded, sameCoded);
        Assert.Equal(coded.GetHashCode(), sameCoded.GetHashCode());
        Assert.NotEqual(coded, uncoded);
    }

    [Fact]
    public void SynthesizedToString_IncludesTheCode_Deliberately()
    {
        var diagnostic = new Diagnostic("boom", DiagnosticSeverity.Error, new SourceSpan(1, 2, 3, 4))
        {
            Code = DiagnosticCode.UnsupportedSemicolon,
        };

        var text = diagnostic.ToString();
        Assert.StartsWith("Diagnostic", text, StringComparison.Ordinal);
        Assert.Contains("Code = UnsupportedSemicolon", text, StringComparison.Ordinal);
    }

    [Fact]
    public void MessageSeverityAndSpan_AreUnchangedByTheCode()
    {
        // The exact pre-M5 observable surface of a known diagnostic: wording,
        // severity, and span byte-for-byte, with the code purely additive.
        var parsed = Parser.Parse("1 ; 2");
        var diagnostic = Assert.Single(parsed.Diagnostics);

        Assert.Equal(
            "Semicolon is not supported as an expression separator. Use comma or adjacency for separate expressions, or parentheses for one sequence value.",
            diagnostic.Message);
        Assert.Equal(DiagnosticSeverity.Error, diagnostic.Severity);
        Assert.Equal(new SourceSpan(1, 3, 1, 3), diagnostic.Span);
        Assert.Equal(DiagnosticCode.UnsupportedSemicolon, diagnostic.Code);
    }

    // ── Family corpus: every source-reachable diagnostic family ─────────────

    /// <summary>
    /// One representative illegal source per source-reachable diagnostic
    /// family — several families deliberately appear more than once to pin
    /// that DISTINCT reporting call sites of one semantic condition share one
    /// code. Each case asserts the expected family is present and that no
    /// KatLang-produced error diagnostic carries the unspecified code.
    /// </summary>
    public static TheoryData<string, string, DiagnosticCode> FamilyCorpus() => new()
    {
        { "unexpected-character", "1 @ 2", DiagnosticCode.UnexpectedCharacter },
        { "unexpected-character-bang", "!x", DiagnosticCode.UnexpectedCharacter },
        { "unterminated-string", "'abc", DiagnosticCode.UnterminatedStringLiteral },
        { "number-too-large", "1e999999", DiagnosticCode.NumberLiteralTooLarge },
        { "unexpected-token-missing-close", "(1", DiagnosticCode.UnexpectedToken },
        { "unexpected-token-trailing-comma", "(3,)", DiagnosticCode.UnexpectedToken },
        { "semicolon-output-row", "1 ; 2", DiagnosticCode.UnsupportedSemicolon },
        { "semicolon-primary", "(; 1)", DiagnosticCode.UnsupportedSemicolon },
        { "duplicate-property", "A = 1\nA = 2", DiagnosticCode.DuplicateProperty },
        { "duplicate-property-public-site", "A = 1\npublic A = 2", DiagnosticCode.DuplicateProperty },
        { "property-declaration-in-parens", "(A = 1, 2)", DiagnosticCode.DeclarationInParentheses },
        { "open-declaration-in-parens", "(open Math)", DiagnosticCode.DeclarationInParentheses },
        { "second-open-declaration", "open Math\nopen Math\n1", DiagnosticCode.InvalidOpenDeclaration },
        { "open-after-property", "A = 1\nopen Math\n1", DiagnosticCode.InvalidOpenDeclaration },
        { "public-open", "public open Math\n1", DiagnosticCode.InvalidOpenDeclaration },
        { "open-in-expression", "x = open\nx", DiagnosticCode.InvalidOpenDeclaration },
        { "open-targets-missing-comma", "open Math Physics\n1", DiagnosticCode.InvalidOpenTargetList },
        { "open-targets-semicolon", "open Math ; Physics\n1", DiagnosticCode.InvalidOpenTargetList },
        { "open-target-on-next-line", "open\nMath", DiagnosticCode.InvalidOpenTargetList },
        { "open-form-number", "open 5\n1", DiagnosticCode.BadOpenForm },
        { "open-form-capture", "M = {\n public C = 5\n}\nR = {\n open (M)\n C\n}\nR", DiagnosticCode.BadOpenForm },
        { "open-form-grace", "M = {public C = 1}\nR = {\n open ~M\n C\n}\nR", DiagnosticCode.BadOpenForm },
        { "open-form-call-dot", "M = {public C = {public D = 1}}\nR = {\n open M.C(1)\n 2\n}\nR", DiagnosticCode.BadOpenForm },
        { "duplicate-branch-pattern", "F(0) = 1\nF(0) = 2\nF(1)", DiagnosticCode.DuplicateBranchPattern },
        { "branch-arity-mismatch", "F(0) = 1\nF(x, y) = 2\nF(1, 2)", DiagnosticCode.BranchArityMismatch },
        { "branch-output-arity-mismatch", "F(0) = 1, 2\nF(x) = 3\nF(1)", DiagnosticCode.BranchOutputArityMismatch },
        { "clause-visibility-mismatch", "public F(0) = 1\nF(x) = 2\nF(1)", DiagnosticCode.ClauseVisibilityMismatch },
        { "grace-on-property-name", "~F = 1\nF", DiagnosticCode.InvalidGraceMarker },
        { "grace-on-non-name", "5~", DiagnosticCode.InvalidGraceMarker },
        { "grace-in-clause-head", "F(x~, 0) = x\nF(1, 0)", DiagnosticCode.InvalidGraceMarker },
        { "collect-marker-detached", "* items = (1, 2)\nitems", DiagnosticCode.InvalidCollectMarker },
        { "collect-marker-repeated", "**items = (1, 2, 3)\nitems", DiagnosticCode.InvalidCollectMarker },
        { "collect-marker-in-expression", "x = *values\nx", DiagnosticCode.InvalidCollectMarker },
        { "collect-marker-pattern-detached", "F(* x) = x\nF(1)", DiagnosticCode.InvalidCollectMarker },
        { "collect-marker-missing-name", "F(*) = 1\nF(2)", DiagnosticCode.InvalidCollectMarker },
        { "two-collecting-per-level", "F(*a, *b) = a\nF(1)", DiagnosticCode.InvalidCollectingBinding },
        { "collecting-in-clause-family", "F(*xs) = 1\nF(0) = 2\nF(3)", DiagnosticCode.InvalidCollectingBinding },
        { "two-collecting-deconstruction", "*a, *b = 1, 2, 3\na", DiagnosticCode.InvalidCollectingBinding },
        { "spread-as-binary-operand", "A = (1, 2)\nA* == A*", DiagnosticCode.MisplacedSpread },
        { "spread-selection", "A = (1, 2)\nA*:0", DiagnosticCode.MisplacedSpread },
        { "if-arity-gate", "if(1, 2)", DiagnosticCode.ArityMismatch },
        { "explicit-params-require-output", "Algo(x, y) = {\n  Prop = 7\n}", DiagnosticCode.ExplicitParametersRequireOutput },
        { "undeclared-in-explicit-list", "F(x) = x + y\nF(1)", DiagnosticCode.UndeclaredIdentifier },
        { "undeclared-in-branch", "F(0) = y\nF(x) = x\nF(0)", DiagnosticCode.UndeclaredIdentifier },
        { "load-elaboration-unavailable", "open 'https://katlang.org/lib.kat'\n1", DiagnosticCode.LoadElaborationUnavailable },
    };

    [Theory]
    [MemberData(nameof(FamilyCorpus))]
    public void KatLangProducedDiagnostics_CarryTheirFamilyCode_AndNeverUnspecified(
        string label, string source, DiagnosticCode expectedCode)
    {
        var parsed = Parser.Parse(source);

        Assert.True(parsed.HasErrors, $"{label}: expected diagnostics, but the source parsed cleanly.");
        Assert.True(
            parsed.Diagnostics.Any(d => d.Severity == DiagnosticSeverity.Error && d.Code == expectedCode),
            $"{label}: no error diagnostic carries {expectedCode}; got: "
            + string.Join(" | ", parsed.Diagnostics.Select(d => $"[{d.Code}] {d.Message}")));
        Assert.All(
            parsed.Diagnostics.Where(d => d.Severity == DiagnosticSeverity.Error),
            d => Assert.NotEqual(DiagnosticCode.Unspecified, d.Code));
    }

    [Fact]
    public void ParserRecursionBudgets_KeepTheirDistinctFamilies()
    {
        // The cumulative container budget (which carries module-loader stack
        // debt) and the per-chain operator budget are DIFFERENT families: the
        // module loader translates only the former into its load-site nesting
        // diagnostic, so collapsing them would change loader classification.
        var deepContainers = new string('(', 400) + "1" + new string(')', 400);
        var containerRejection = Parser.Parse(deepContainers);
        Assert.Contains(containerRejection.Diagnostics, d => d.Code == DiagnosticCode.NestingTooDeep);

        var deepChain = "x = " + string.Join("+", Enumerable.Repeat("1", 300)) + "\nx";
        var chainRejection = Parser.Parse(deepChain);
        Assert.Contains(chainRejection.Diagnostics, d => d.Code == DiagnosticCode.ExpressionChainTooDeep);
    }

    [Fact]
    public void DistinctSemanticFamilies_ProduceDistinctCodes()
    {
        // A host must be able to react differently to a duplicate property
        // definition than to a duplicate conditional branch pattern (and so on
        // for every family pair in the corpus): the corpus expectation column
        // itself spans many codes, so two families never collapse silently.
        var duplicateProperty = Assert.Single(
            Parser.Parse("A = 1\nA = 2").Diagnostics, d => d.Severity == DiagnosticSeverity.Error);
        var duplicateBranch = Assert.Single(
            Parser.Parse("F(0) = 1\nF(0) = 2\nF(1)").Diagnostics, d => d.Severity == DiagnosticSeverity.Error);
        Assert.NotEqual(duplicateProperty.Code, duplicateBranch.Code);

        var distinctExpectedFamilies = FamilyCorpus()
            .Select(row => (DiagnosticCode)row[2])
            .Distinct()
            .Count();
        Assert.True(distinctExpectedFamilies >= 20,
            $"The family corpus should span the taxonomy; it covers only {distinctExpectedFamilies} codes.");
    }

    // ── Factory-backed families not reachable from plain source ─────────────

    [Fact]
    public void StructuralPreflightDiagnostics_CarryDepthAndCycleCodes()
    {
        var depth = AstStructuralPreflight.ToParseDiagnostic(
            new AstStructuralRejection(AstStructuralViolation.DepthExceeded, new SourceSpan(1, 1, 1, 1)),
            limit: 300);
        Assert.Equal(DiagnosticCode.AstDepthLimitExceeded, depth.Code);

        var cycle = AstStructuralPreflight.ToParseDiagnostic(
            new AstStructuralRejection(AstStructuralViolation.CycleDetected, new SourceSpan(1, 1, 1, 1)),
            limit: 300);
        Assert.Equal(DiagnosticCode.AstCycleDetected, cycle.Code);
    }

    [Fact]
    public void SourceProcessingDiagnosticFactories_CarryTheirFamilyCodes()
    {
        Assert.Equal(
            DiagnosticCode.SourceLengthExceeded,
            SourceProcessingDiagnostics.SourceLengthExceeded(10, 5).Code);
        Assert.Equal(
            DiagnosticCode.SourceLengthExceeded,
            SourceProcessingDiagnostics.ModuleSourceLengthExceeded("https://katlang.org/m.kat", 10, 5, null).Code);
        Assert.Equal(
            DiagnosticCode.AggregateSourceLengthExceeded,
            SourceProcessingDiagnostics.AggregateSourceLengthExceeded("https://katlang.org/m.kat", 10, 20, 15, null).Code);
        Assert.Equal(
            DiagnosticCode.AggregateSourceLengthExceeded,
            SourceProcessingDiagnostics.AggregateSourceLengthExceededByProgram(10, 5).Code);
        Assert.Equal(
            DiagnosticCode.ModuleImportDepthExceeded,
            SourceProcessingDiagnostics.ModuleImportDepthExceeded("https://katlang.org/m.kat", 3, 2, null).Code);
        Assert.Equal(
            DiagnosticCode.ModuleCountExceeded,
            SourceProcessingDiagnostics.ModuleCountExceeded("https://katlang.org/m.kat", 3, 2, null).Code);
        Assert.Equal(
            DiagnosticCode.ModuleNestingTooDeep,
            SourceProcessingDiagnostics.ModuleNestingTooDeep("https://katlang.org/m.kat", 300, null).Code);
        Assert.Equal(
            DiagnosticCode.ModuleElaborationStackExhausted,
            SourceProcessingDiagnostics.ModuleElaborationStackExhausted(300).Code);
    }

    [Fact]
    public void LoadElaborationGuardDiagnostics_CarryTheirFamilyCodes()
    {
        var root = Parser.ParseSyntax("open 'https://katlang.org/lib.kat'\n1").SyntaxRoot;

        var unavailable = LoadElaborationGuard.CreateUnavailableDiagnostics(root);
        Assert.NotEmpty(unavailable);
        Assert.All(unavailable, d => Assert.Equal(DiagnosticCode.LoadElaborationUnavailable, d.Code));

        var invariant = LoadElaborationGuard.CreatePostElaborationInvariantDiagnostic(root);
        Assert.Equal(DiagnosticCode.InternalError, invariant.Code);
    }

    // ── Module-loading families and metadata survival through the loader ────

    private static RunOptions Loader(Func<string, string> map, SourceProcessingLimits? limits = null) => new()
    {
        DownloadCode = (url, _) => ValueTask.FromResult(map(url)),
        SourceProcessingLimits = limits,
    };

    private static async Task<IReadOnlyList<KatLangError>> LoadFailureErrorsAsync(string source, RunOptions options)
    {
        var failure = Assert.IsType<RunResult.ParseFailure>(await KatLangEngine.RunAsync(source, options));
        return failure.Errors;
    }

    [Fact]
    public async Task ModuleLoadingFailures_ClassifyWithoutMessageInspection()
    {
        const string Program = "open 'https://katlang.org/x.kat'\n1";

        var fetchThrew = await LoadFailureErrorsAsync(Program, new RunOptions
        {
            DownloadCode = (_, _) => throw new InvalidOperationException("boom"),
        });
        Assert.Contains(fetchThrew, e => e.Code == KatLangErrorCode.LoadFetchFailed);

        var fetchEmpty = await LoadFailureErrorsAsync(Program, Loader(_ => null!));
        Assert.Contains(fetchEmpty, e => e.Code == KatLangErrorCode.LoadFetchFailed);

        var htmlBody = await LoadFailureErrorsAsync(Program, Loader(_ => "<html><body>hi</body></html>"));
        Assert.Contains(htmlBody, e => e.Code == KatLangErrorCode.InvalidLoadedSource);

        var cycle = await LoadFailureErrorsAsync(Program, Loader(_ => "open 'https://katlang.org/x.kat'\nA = 1"));
        Assert.Contains(cycle, e => e.Code == KatLangErrorCode.LoadCycle);

        var httpScheme = await LoadFailureErrorsAsync("open 'http://katlang.org/x.kat'\n1", Loader(_ => "A = 1"));
        Assert.Contains(httpScheme, e => e.Code == KatLangErrorCode.InvalidLoadUrl);

        var badDomain = await LoadFailureErrorsAsync("open 'https://evil.example/x.kat'\n1", Loader(_ => "A = 1"));
        Assert.Contains(badDomain, e => e.Code == KatLangErrorCode.InvalidLoadUrl);

        var depth = await LoadFailureErrorsAsync(
            "open 'https://katlang.org/a.kat'\n1",
            Loader(
                url => url.Contains("a.kat", StringComparison.Ordinal)
                    ? "open 'https://katlang.org/b.kat'\nX = 1"
                    : "Y = 2",
                new SourceProcessingLimits { MaxModuleDepth = 1 }));
        Assert.Contains(depth, e => e.Code == KatLangErrorCode.ModuleImportDepthExceeded);

        var moduleCount = await LoadFailureErrorsAsync(
            "P = {open 'https://katlang.org/a.kat'\n1}\nQ = {open 'https://katlang.org/b.kat'\n2}\nP, Q",
            Loader(_ => "Z = 1", new SourceProcessingLimits { MaxModuleCount = 1 }));
        Assert.Contains(moduleCount, e => e.Code == KatLangErrorCode.ModuleCountExceeded);

        var aggregate = await LoadFailureErrorsAsync(
            "open 'https://katlang.org/a.kat'\n1",
            Loader(_ => "W = 1234567890", new SourceProcessingLimits { MaxAggregateSourceLength = 40 }));
        Assert.Contains(aggregate, e => e.Code == KatLangErrorCode.AggregateSourceLengthExceeded);

        var moduleSource = await LoadFailureErrorsAsync(
            "open 'https://katlang.org/a.kat'\n1",
            Loader(_ => "V = 123456789012345678901234567890", new SourceProcessingLimits { MaxSourceLength = 33 }));
        Assert.Contains(moduleSource, e => e.Code == KatLangErrorCode.SourceLengthExceeded);

        var dynamicUrl = await LoadFailureErrorsAsync(
            "Url = 'https://katlang.org/a.kat'\nLib = load(Url)\nLib",
            Loader(_ => "A = 1"));
        Assert.Contains(dynamicUrl, e => e.Code == KatLangErrorCode.InvalidLoadDirective);

        var runtimePosition = await LoadFailureErrorsAsync(
            "Lib = load('https://katlang.org/a.kat') + 1\nLib",
            Loader(_ => "A = 1"));
        Assert.Contains(runtimePosition, e => e.Code == KatLangErrorCode.InvalidLoadDirective);

        var multipleArguments = await LoadFailureErrorsAsync(
            "Lib = load('https://katlang.org/a.kat', 'https://katlang.org/b.kat')\nLib",
            Loader(_ => "A = 1"));
        Assert.Contains(multipleArguments, e => e.Code == KatLangErrorCode.InvalidLoadDirective);
    }

    /// <summary>
    /// The module loader's nested-parse triage — "position-dependent nesting
    /// rejection" vs "invalid module content" — is now classified by the nested
    /// diagnostics' structured codes instead of message substrings. Both
    /// branches must keep their established load-site messages AND expose their
    /// structured families.
    /// </summary>
    [Fact]
    public async Task NestedModuleParseTriage_UsesStructuredCodes_NotMessageText()
    {
        var deepModule = "D = " + new string('(', 400) + "1" + new string(')', 400);
        var nesting = await LoadFailureErrorsAsync(
            "open 'https://katlang.org/deep.kat'\n1", Loader(_ => deepModule));
        var nestingError = Assert.Single(nesting);
        Assert.Equal(KatLangErrorCode.ModuleNestingTooDeep, nestingError.Code);
        Assert.Contains("would nest module source too deeply", nestingError.Message, StringComparison.Ordinal);

        var invalid = await LoadFailureErrorsAsync(
            "open 'https://katlang.org/bad.kat'\n1", Loader(_ => "D = ("));
        var invalidError = Assert.Single(invalid);
        Assert.Equal(KatLangErrorCode.InvalidLoadedSource, invalidError.Code);
        Assert.Contains("not valid KatLang source", invalidError.Message, StringComparison.Ordinal);
    }

}
