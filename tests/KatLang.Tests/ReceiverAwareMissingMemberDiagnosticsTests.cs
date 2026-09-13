namespace KatLang.Tests;

/// <summary>
/// G-24 — receiver-aware diagnostics for a misspelled member on a statically
/// known receiver.
///
/// <para>Dot syntax is receiver injection: <c>a.F(args)</c> is <c>F(a, args)</c>
/// whenever <c>a</c> has no structural <c>F</c>, and a statically known receiver
/// (<c>Math</c>, a block, a module) has no special status. So <c>Math.Ceiling(2.1)</c>
/// is not a missing-member error: the edge falls back to a lexical <c>Ceiling</c>,
/// and since none is visible the name is inferred as an implicit parameter — a
/// report that used to read like an ordinary unresolved name. The detector now
/// records the dot-member origin on the SAME diagnostic-only provenance the
/// promotion already produced (<see cref="ImplicitParameterProvenance.DotMemberOrigin"/>),
/// the rendered report leads with the receiver-aware explanation, the
/// suggestion comes from the receiver's own member surface, and a single such
/// parameter is positioned at the member token.</para>
///
/// <para>Everything here is diagnostics-only, and these tests pin that too:
/// <c>a.F(args) ≡ F(a, args)</c> stays the rule, valid lexical fallback on a
/// known receiver stays valid, opaque-receiver inference is untouched, and
/// bare-name reports are byte-identical to before.</para>
/// </summary>
public class ReceiverAwareMissingMemberDiagnosticsTests
{
    private static Expr Program(string source)
        => new Expr.AlgorithmExpr(SourceProvenance.ParseValid(source).Root);

    private static EvalError Innermost(EvalError error)
    {
        while (error is EvalError.WithContext context)
            error = context.Inner;

        return error;
    }

    /// <summary>
    /// Fails the source under BOTH plain and counted evaluation, requires one
    /// shared rendered message (plain/counted diagnostic parity), and returns
    /// the plain error for structured assertions.
    /// </summary>
    private static (string Message, EvalError PlainError) FailWithParity(string source)
    {
        var program = Program(source);

        var plain = Evaluator.Run(program);
        Assert.True(plain.IsError, $"expected plain evaluation failure for: {source}");

        var counted = Evaluator.RunCounted(program);
        Assert.True(counted.IsError, $"expected counted evaluation failure for: {source}");

        var plainMessage = KatLangError.FromEvalError(plain.Error).Message;
        var countedMessage = KatLangError.FromEvalError(counted.Error).Message;
        Assert.Equal(plainMessage, countedMessage);
        Assert.Equal(plain.Error.Span, counted.Error.Span);

        return (plainMessage, plain.Error);
    }

    private static ImplicitParameterProvenance SingleNote(EvalError error)
    {
        var notes = Innermost(error) switch
        {
            EvalError.UnresolvedImplicitParams unresolved => unresolved.InferredImplicitParameters,
            EvalError.ArityMismatch arity => arity.InferredImplicitParameters,
            var other => throw new Xunit.Sdk.XunitException(
                $"expected an arity/unresolved-implicit-params error, got {other.GetType().Name}"),
        };

        Assert.NotNull(notes);
        return Assert.Single(notes);
    }

    private static string Display(string source)
        => Assert.IsType<RunResult.Success>(KatLangEngine.Run(source)).ToDisplayString().ReplaceLineEndings("\n");

    private static KatLangError EngineFailure(string source)
        => Assert.Single(Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(source)).Errors);

    private const string MathCeilingTypo = "Math.Ceiling(2.1)";

    private const string MathCeilingTypoMessage =
        "Property 'Ceiling' was not found on `Math`, so the dotted call fell back to a lexical callable named 'Ceiling'. "
        + "That name does not resolve to a property or other visible name here, so KatLang interprets it as an implicit parameter. "
        + "Its value is provided by the caller. No argument was provided, so the program cannot be executed (expected 1 argument, got 0).\n"
        + "Did you mean 'Math.Ceil'?";

    // ── 1. Known Math receiver typo ────────────────────────────────────────

    [Fact]
    public void MathReceiverTypo_FailsThroughUnresolvedImplicitParameterWithReceiverAwareReport()
    {
        var (message, error) = FailWithParity(MathCeilingTypo);

        // Still the ordinary unresolved-implicit-parameter failure — same
        // structured kind, same context, same code — enriched, not replaced.
        var contextual = Assert.IsType<EvalError.WithContext>(error);
        var context = Assert.IsType<ImplicitParameterContext>(contextual.ErrorContext);
        Assert.Equal(["Ceiling"], context.ParamNames);
        var unresolved = Assert.IsType<EvalError.UnresolvedImplicitParams>(contextual.Inner);
        Assert.Equal(["Ceiling"], unresolved.ParamNames);
        Assert.Equal(KatLangErrorCode.UnresolvedImplicitParams, error.Code);

        var note = SingleNote(error);
        Assert.Equal("Ceiling", note.Name);
        Assert.Equal("Math", Assert.IsType<DotMemberFallbackOrigin>(note.DotMemberOrigin).ReceiverDescription);
        Assert.Equal("Math.Ceil", note.SuggestedName);

        Assert.Equal(MathCeilingTypoMessage, message);
    }

    [Fact]
    public void MathReceiverTypo_IsPositionedAtTheMissingMemberToken()
    {
        var (_, error) = FailWithParity(MathCeilingTypo);

        // `Math.Ceiling(2.1)`: the member identifier starts at column 6; the
        // whole first output row (the former position) starts at column 1.
        var note = SingleNote(error);
        Assert.NotNull(note.Span);
        Assert.Equal(1, note.Span!.StartLineNumber);
        Assert.Equal(6, note.Span.StartColumn);
        Assert.Equal(note.Span, error.Span);
        Assert.Equal(note.Span, Innermost(error).Span);

        var engineError = EngineFailure(MathCeilingTypo);
        Assert.Equal(1, engineError.StartLine);
        Assert.Equal(6, engineError.StartColumn);
        Assert.Equal(note.Span.EndColumn, engineError.EndColumn);
        Assert.Equal(MathCeilingTypoMessage, engineError.Message);
    }

    [Fact]
    public async Task MathReceiverTypo_AsyncEngineMatchesSync()
    {
        var syncError = EngineFailure(MathCeilingTypo);
        var asyncFailure = Assert.IsType<RunResult.EvalFailure>(await KatLangEngine.RunAsync(MathCeilingTypo));
        var asyncError = Assert.Single(asyncFailure.Errors);

        Assert.Equal(syncError.Message, asyncError.Message);
        Assert.Equal(syncError.StartLine, asyncError.StartLine);
        Assert.Equal(syncError.StartColumn, asyncError.StartColumn);
        Assert.Equal(syncError.Code, asyncError.Code);
    }

    [Fact]
    public void MathReceiverTypo_ResolutionIsUnchanged_TheParameterStillBindsAnArgument()
    {
        // The suggestion never wins resolution: `Ceiling` is an ordinary
        // implicit parameter, so a caller supplies it and the fallback call
        // `Ceiling(Math, 2.1)` runs with that callable — never `Math.Ceil`.
        var parsed = SourceProvenance.ParseValid("P = Math.Ceiling(2.1)\nTwice(a, b) = b * 2\nP(Twice)");
        Assert.Empty(parsed.Diagnostics);
        var p = Assert.Single(parsed.Root.Properties, property => property.Name == "P").Value;
        Assert.Equal(["Ceiling"], p.Params);

        Assert.Equal("4.2", Display("P = Math.Ceiling(2.1)\nTwice(a, b) = b * 2\nP(Twice)"));
        Assert.Equal("3", Display("Math.Ceil(2.1)"));
    }

    // ── 2. Misleading lexical suggestion suppression ───────────────────────

    [Fact]
    public void MathMinTypo_DoesNotSuggestTheUnrelatedLexicalBuiltin()
    {
        var (message, error) = FailWithParity("Math.Min(1, 2)");

        var note = SingleNote(error);
        Assert.Equal("Math", note.DotMemberOrigin?.ReceiverDescription);
        // No Math member is a plausible respelling of `Min` (`Sin` does not keep
        // the initial), and the lexical collection builtin `min` is unrelated
        // to Math's member surface: no suggestion beats a misleading one.
        Assert.Null(note.SuggestedName);
        Assert.DoesNotContain("Did you mean", message, StringComparison.Ordinal);
        Assert.DoesNotContain("'min'", message, StringComparison.Ordinal);
        Assert.StartsWith(
            "Property 'Min' was not found on `Math`, so the dotted call fell back to a lexical callable named 'Min'. That name does not resolve",
            message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void LexicalBuiltinStaysTheSuggestion_WhereTheNameIsNotAnApparentMemberAccess()
    {
        // Controls for the case above: the same lexical near-miss IS offered
        // for a bare name, and for a dotted name on a MEMBERLESS receiver (a
        // plain value property), where the dotted call is necessarily the
        // extension call `min(S)` the writer most plausibly meant.
        Assert.Equal("min", SingleNote(FailWithParity("Min").PlainError).SuggestedName);

        var (message, error) = FailWithParity("S = (1, 2, 3)\nS.Min");
        var note = SingleNote(error);
        Assert.Equal("S", note.DotMemberOrigin?.ReceiverDescription);
        Assert.Equal("min", note.SuggestedName);
        Assert.EndsWith("Did you mean 'min'?", message, StringComparison.Ordinal);
    }

    // ── 3. User-defined known block typo: the same mechanism ───────────────

    private const string LibDubelTypo = "Lib = {\n    public Double(x) = 2 * x\n}\n\nLib.Dubel(4)";

    [Fact]
    public void UserBlockReceiverTypo_UsesTheSameGenericMechanism()
    {
        var (message, error) = FailWithParity(LibDubelTypo);

        Assert.IsType<EvalError.UnresolvedImplicitParams>(Innermost(error));
        var note = SingleNote(error);
        Assert.Equal("Dubel", note.Name);
        Assert.Equal("Lib", note.DotMemberOrigin?.ReceiverDescription);
        Assert.Equal("Lib.Double", note.SuggestedName);
        Assert.Equal(5, note.Span!.StartLineNumber);
        Assert.Equal(5, note.Span.StartColumn);
        Assert.Equal(note.Span, error.Span);

        Assert.Equal(
            "Property 'Dubel' was not found on `Lib`, so the dotted call fell back to a lexical callable named 'Dubel'. "
            + "That name does not resolve to a property or other visible name here, so KatLang interprets it as an implicit parameter. "
            + "Its value is provided by the caller. No argument was provided, so the program cannot be executed (expected 1 argument, got 0).\n"
            + "Did you mean 'Lib.Double'?",
            message);
    }

    [Fact]
    public void ChainedKnownReceiver_IsDescribedAsWrittenAndSuggestsItsNestedMember()
    {
        var (message, error) = FailWithParity(
            "Lib = {\n    public Sub = {\n        public Quotient(x) = x\n    }\n}\nLib.Sub.Qoutient(4)");

        var note = SingleNote(error);
        Assert.Equal("Lib.Sub", note.DotMemberOrigin?.ReceiverDescription);
        Assert.Equal("Lib.Sub.Quotient", note.SuggestedName);
        Assert.StartsWith("Property 'Qoutient' was not found on `Lib.Sub`, so the dotted call", message, StringComparison.Ordinal);
        Assert.EndsWith("Did you mean 'Lib.Sub.Quotient'?", message, StringComparison.Ordinal);
    }

    // ── 4. Closed parameter list: the existing good diagnostic is untouched ─

    [Fact]
    public void ClosedParameterList_KeepsTheRuntimeMissingMemberDiagnostic()
    {
        const string source = "F(x) = Math.Ceiling(x)\nF(2.1)";
        var parsed = SourceProvenance.ParseValid(source);
        Assert.Equal(["x"], Assert.Single(parsed.Root.Properties).Value.Params);

        var result = parsed.Evaluate();
        Assert.True(result.IsError);
        var unknown = Assert.IsType<EvalError.UnknownName>(Innermost(result.Error));
        Assert.Equal("Ceiling", unknown.Name);
        Assert.Equal(KatLangErrorCode.UnknownName, result.Error.Code);

        var message = KatLangError.FromEvalError(result.Error).Message;
        Assert.Equal(
            "while evaluating call to F: Property 'Ceiling' was not found on `Math`, and no visible algorithm or property "
            + "named 'Ceiling' can be used with `Math` as the first argument.",
            message);
        Assert.DoesNotContain("implicit parameter", message, StringComparison.Ordinal);
    }

    // ── 5. Valid lexical fallback on a known receiver survives ─────────────

    [Fact]
    public void KnownReceiverLexicalFallback_StaysValidWithoutWarningOrError()
    {
        const string source = "Ceiling(a, b) = b * 2\nMath.Ceiling(2.1)";
        var parsed = SourceProvenance.ParseValid(source);
        Assert.Empty(parsed.Diagnostics);
        // Nothing is inferred: `Ceiling` resolves lexically, so the root has no parameters.
        Assert.Empty(parsed.Root.Params);

        // `Math.Ceiling(2.1)` is the ordinary fallback call `Ceiling(Math, 2.1)`.
        Assert.Equal("4.2", Display(source));
    }

    [Fact]
    public void UserDefinedKnownReceiverLexicalFallback_StaysValid()
    {
        Assert.Equal("12", Display("Lib = {\n    public Double(x) = 2 * x\n}\nDubel(a, b) = b * 3\nLib.Dubel(4)"));

        // A member-bearing receiver with a zero-argument extension: `Lib.Describe` is `Describe(Lib)`.
        Assert.Equal("1", Display("Lib = {\n    public Double(x) = 2 * x\n}\nDescribe(lib) = 1\nLib.Describe"));
    }

    // ── 6. Opaque receiver inference survives ──────────────────────────────

    [Fact]
    public void OpaqueReceiver_KeepsHigherOrderImplicitInference()
    {
        var parsed = SourceProvenance.ParseValid("K = a.t\nK(7, {a+1})");
        Assert.Equal(["a", "t"], Assert.Single(parsed.Root.Properties).Value.Params);
        Assert.Equal("8", Display("K = a.t\nK(7, {a+1})"));

        // The receiver is not statically known, so nothing claims it lacks `t`:
        // the zero-argument demand of K reports the ordinary arity note with no
        // receiver-aware origin and no member suggestion.
        var (message, error) = FailWithParity("K = a.t\nK");
        var arity = Assert.IsType<EvalError.ArityMismatch>(Innermost(error));
        Assert.All(arity.InferredImplicitParameters!, note => Assert.Null(note.DotMemberOrigin));
        Assert.All(arity.InferredImplicitParameters!, note => Assert.Null(note.SuggestedName));
        Assert.Equal(
            "Property 'K' expects 2 parameters, but was called with 0 arguments.\n"
            + "An implicit parameter 'a' was inferred at [1:5].\n"
            + "An implicit parameter 't' was inferred at [1:7].",
            message);

        Assert.Equal(KatLangErrorCode.NotAnAlgorithm, EngineFailure("K = a.t\nK(3, 4)").Code);
    }

    // ── 7. A dotted fallback that a visible callable satisfies keeps working ─

    [Fact]
    public void GenuineLexicalDottedFallback_OnValueReceivers_IsUnchanged()
    {
        Assert.Equal("5", Display("N = 5\nN.abs"));
        Assert.Equal("3", Display("S = (1, 2, 3)\nS.count"));
        Assert.Equal("50", Display("A = x + 7\nB = x * 5\n3.A.B"));
    }

    // ── 8. No regression for ordinary unresolved names ─────────────────────

    [Fact]
    public void BareNameInference_AndItsLexicalSuggestion_AreUnchanged()
    {
        var (message, error) = FailWithParity("Valeu = 3\nValue + 1");

        var note = SingleNote(error);
        Assert.Null(note.DotMemberOrigin);
        Assert.Equal("Valeu", note.SuggestedName);
        // The ordinary position: the first output row, not the name.
        Assert.Equal(2, error.Span!.StartLineNumber);
        Assert.Equal(1, error.Span.StartColumn);
        Assert.Equal(
            "Identifier 'Value' does not resolve to a property or other visible name here, so KatLang interprets it as an implicit parameter. "
            + "Its value is provided by the caller. No argument was provided, so the program cannot be executed (expected 1 argument, got 0).\n"
            + "Did you mean 'Valeu'?",
            message);

        var engineError = EngineFailure("x + 1");
        Assert.Equal(1, engineError.StartColumn);
        Assert.StartsWith("Identifier 'x' does not resolve to a property or other visible name here", engineError.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void BareFirstOccurrence_KeepsTheOrdinaryReport()
    {
        // Provenance is the FIRST occurrence; here the bare `Ceiling` comes
        // before the dotted one, so the name is an ordinary unresolved name.
        var (message, error) = FailWithParity("Ceiling + Math.Ceiling(2.1)");

        var note = SingleNote(error);
        Assert.Null(note.DotMemberOrigin);
        Assert.Equal(1, error.Span!.StartColumn);
        Assert.StartsWith("Identifier 'Ceiling' does not resolve", message, StringComparison.Ordinal);
        Assert.DoesNotContain("was not found on", message, StringComparison.Ordinal);
    }

    // ── Several unresolved names: receiver-aware notes are appended per name ─

    [Fact]
    public void MultipleUnresolvedNames_AppendTheReceiverAwareNoteForTheDotOrigin()
    {
        var (message, error) = FailWithParity("Math.Ceiling(x)");

        // Two names: the position stays the ordinary first output row.
        Assert.Equal(1, error.Span!.StartColumn);
        Assert.Equal(
            "Identifiers 'Ceiling' and 'x' do not resolve to properties or other visible names here, so KatLang interprets them as implicit parameters. "
            + "Their values are provided by the caller. No arguments were provided, so the program cannot be executed (expected 2 arguments, got 0).\n"
            + "Property 'Ceiling' was not found on `Math` at [1:6], so the dotted call fell back to a lexical callable named 'Ceiling'.\n"
            + "Did you mean 'Math.Ceil' instead of 'Ceiling'?",
            message);
    }

    // ── Arity mismatches carry the same receiver-aware note ────────────────

    [Fact]
    public void PropertyValueDemand_ArityNoteCarriesTheReceiverAwareOrigin()
    {
        var (message, error) = FailWithParity("P = Math.Ceiling(2.1)\nP");

        Assert.IsType<EvalError.ArityMismatch>(Innermost(error));
        Assert.Equal(
            "Property 'P' expects 1 parameter, but was called with 0 arguments.\n"
            + "An implicit parameter 'Ceiling' was inferred at [1:10].\n"
            + "Property 'Ceiling' was not found on `Math`, so the dotted call fell back to a lexical callable named 'Ceiling'.\n"
            + "Did you mean 'Math.Ceil'?",
            message);
    }

    [Fact]
    public void SignatureBearingCall_AppendsTheReceiverAwareNoteEvenWithoutASuggestion()
    {
        // The signature shows the name `Min` but not WHY it is a parameter;
        // the receiver-aware note explains it, and nothing misleading is suggested.
        var (message, _) = FailWithParity("Use = Math.Min(1, 2)\nUse()");

        Assert.Equal(
            "Callable `Use(Min)` expects 1 argument, but was called with 0 arguments.\n"
            + "An implicit parameter 'Min' was inferred at [1:12].\n"
            + "Property 'Min' was not found on `Math`, so the dotted call fell back to a lexical callable named 'Min'.",
            message);
    }

    // ── Memberless known receivers keep the lexical policy ─────────────────

    [Fact]
    public void MemberlessKnownReceiver_KeepsTheLexicalSuggestionUnderTheReceiverAwarePreface()
    {
        var (message, error) = FailWithParity("S = (1, 2, 3)\nS.Count");

        var note = SingleNote(error);
        Assert.Equal("S", note.DotMemberOrigin?.ReceiverDescription);
        Assert.Equal("count", note.SuggestedName);
        Assert.Equal(2, error.Span!.StartLineNumber);
        Assert.Equal(3, error.Span.StartColumn);
        Assert.StartsWith(
            "Property 'Count' was not found on `S`, so the dotted call fell back to a lexical callable named 'Count'. That name does not resolve",
            message,
            StringComparison.Ordinal);
        Assert.EndsWith("Did you mean 'count'?", message, StringComparison.Ordinal);
    }

    // ── Member-typo policy: plausible members only, no receiver spelling involved ─

    [Theory]
    [InlineData("Math.Ceiling(2.1)", "Math.Ceil")]   // three edits over seven characters
    [InlineData("Math.Ciel(2.1)", "Math.Ceil")]      // adjacent transposition
    [InlineData("Math.Sqr(9)", "Math.Sqrt")]         // one deletion, unique among S-members
    [InlineData("Math.Floo(1)", "Math.Floor")]
    [InlineData("Math.Cosine(1)", "Math.Cos")]
    [InlineData("Math.Min(1, 2)", null)]             // `Sin` does not keep the initial letter
    [InlineData("Math.Max(1, 2)", null)]
    [InlineData("Math.Sgn(1)", null)]                // `Sign` and `Sin` tie: no arbitrary pick
    [InlineData("Math.Logarithm(8)", null)]          // too far under the capped member threshold
    public void MemberTypoPolicy_SuggestsOnlyPlausibleReceiverMembers(string source, string? expectedSuggestion)
        => Assert.Equal(expectedSuggestion, SingleNote(FailWithParity(source).PlainError).SuggestedName);

    [Theory]
    [InlineData("Lib.Dubel(4)", "Lib.Double")]
    [InlineData("Lib.Duoble(4)", "Lib.Double")]
    [InlineData("Lib.Dbl(4)", null)]
    [InlineData("Lib.Half(4)", null)]
    public void MemberTypoPolicy_AppliesIdenticallyToAUserBlock(string call, string? expectedSuggestion)
    {
        var note = SingleNote(FailWithParity($"Lib = {{\n    public Double(x) = 2 * x\n}}\n{call}").PlainError);

        Assert.Equal("Lib", note.DotMemberOrigin?.ReceiverDescription);
        Assert.Equal(expectedSuggestion, note.SuggestedName);
    }

    // ── The metadata stays internal and structurally invisible ─────────────

    [Fact]
    public void FilteredMemberSurface_DoesNotFallBackToLexicalSuggestions()
    {
        var root = SourceProvenance.ParseValid("Outer(seed) = { Lib = { public Value = seed }\nLib }\n0").Root;
        var outer = Assert.Single(root.Properties).Value;
        var lib = Assert.Single(outer.Properties).Value;
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, Assert.Single(lib.Properties).Exposure);

        Assert.Null(NameSuggestions.SuggestVisibleName(
            "Min", ElaboratedScopeLookup.CreateScope(root,
                ElaboratedScopeLookup.CreateScope(BuiltinRegistry.CreateSemanticPreludeAlgorithm())), ParameterOwnership.Empty,
            new DotMemberReceiver(lib, "Lib")));
    }

    [Fact]
    public void MemberBeyondSuggestionLengthBound_DoesNotMakeReceiverMemberless()
    {
        var source = $"Lib = {{ public {new string('M', 65)} = 1 }}\nLib.Min";
        Assert.Null(SingleNote(FailWithParity(source).PlainError).SuggestedName);
    }

    [Theory]
    [InlineData("Oduble")]
    [InlineData("Rouble")]
    public void LongMemberWithOneInitialEdit_StillOffersTheUniqueCorrection(string typo)
        => Assert.Equal("Lib.Double", SingleNote(FailWithParity(
            $"Lib = {{ public Double(x) = x * 2 }}\nLib.{typo}(4)").PlainError).SuggestedName);

    [Fact]
    public void OwnershipCompletion_DoesNotRetainAFormerlyKnownReceiverOrigin()
    {
        const string source = "Providers = { public Lib = { public Double(x) = x * 2 } }\n"
            + "Outer = { Inner = { open Providers\nLib.Dubel(4) }\nNeed = Lib\nInner + Need }\nOuter";
        var root = SourceProvenance.ParseValid(source).Root;
        var outer = Assert.Single(root.Properties, property => property.Name == "Outer").Value;
        var inner = Assert.Single(outer.Properties, property => property.Name == "Inner").Value;
        Assert.IsType<Expr.Param>(Assert.IsType<Expr.DotCall>(Assert.Single(inner.Output)).Target);
        var note = Assert.Single(inner.Parameters).InferredProvenance!;
        Assert.Equal("Dubel", note.Name);
        Assert.Null(note.DotMemberOrigin);
        Assert.Null(note.SuggestedName);
    }

    [Theory]
    [InlineData("Lib.Sub.Quotent(4)", 1, 9)]
    [InlineData("(Lib.Sub).Quotent(4)", 1, 11)]
    [InlineData("Lib\n.Sub\n.Quotent(4)", 3, 2)]
    public void NestedReceiverSpan_IsExactlyTheWrittenMember(string expression, int line, int column)
    {
        const string definitions = "Lib = { public Sub = { public Quotient(x) = x } }\n";
        var (_, error) = FailWithParity(definitions + expression);
        var note = SingleNote(error);
        Assert.Equal("Lib.Sub.Quotient", note.SuggestedName);
        Assert.Equal(new SourceSpan(line + 1, column, line + 1, column + "Quotent".Length - 1), error.Span);
    }

    [Fact]
    public void DotOrigin_SurvivesTransitiveLiftingAndPatternCloning()
    {
        const string source = "Lib = { public Double(x) = x * 2 }\nUse = Lib.Dubel(4)\nBridge = Use + 1\nHelper = Bridge + 1\nHelper";
        var root = SourceProvenance.ParseValid(source).Root;
        var helper = Assert.Single(root.Properties, property => property.Name == "Helper").Value;
        var parameter = Assert.Single(helper.Parameters);
        var clone = parameter with { };
        Assert.Same(parameter.InferredProvenance, clone.InferredProvenance);
        Assert.Same(parameter.InferredProvenance, clone.ToPattern().InferredProvenance);
        var (_, error) = FailWithParity(source);
        var note = SingleNote(error);
        Assert.Equal("Lib", note.DotMemberOrigin?.ReceiverDescription);
        Assert.Equal("Lib.Double", note.SuggestedName);
        Assert.Equal(new SourceSpan(2, 11, 2, 15), note.Span);
    }

    [Fact]
    public void ExposureCompletion_DoesNotSuggestAMemberOfTheFormerOpenedReceiver()
    {
        const string source = "open Good\nGood = { public Lib = { public Other = 1 } }\n"
            + "Outer(seed) = { Bad = { public Lib = { public Double(x) = x * 2\nseed } }\n"
            + "Inner = { open Bad\nLib.Dubel(4) }\nInner }\nOuter(1)";
        var (_, error) = FailWithParity(source);
        Assert.Null(SingleNote(error).SuggestedName);
    }

    [Fact]
    public void DotRecordClone_PreservesMetadataWithoutChangingIdentity()
    {
        var dot = Assert.IsType<Expr.DotCall>(Assert.Single(SourceProvenance.ParseValid(MathCeilingTypo).Root.Output));
        var note = DiagnosticRecordMetadata<ImplicitParameterProvenance>.Get(dot);
        Assert.NotNull(note);
        var clone = dot with { };
        Assert.Same(note, DiagnosticRecordMetadata<ImplicitParameterProvenance>.Get(clone));
        DiagnosticRecordMetadata<ImplicitParameterProvenance>.Set(clone, null);
        Assert.Equal(dot, clone);
        Assert.Equal(dot.GetHashCode(), clone.GetHashCode());
        Assert.Equal(dot.ToString(), clone.ToString());
    }

    [Fact]
    public async Task SuspendedModuleLoad_KeepsTheLocalMemberSpanAndQualifiedSuggestion()
    {
        var download = new TaskCompletionSource<string>(TaskCreationOptions.RunContinuationsAsynchronously);
        var pending = KatLangEngine.RunAsync("Lib = load('https://katlang.org/g24.kat')\nLib.Dubel(4)",
            new RunOptions { DownloadCode = (_, _) => new ValueTask<string>(download.Task) });
        Assert.False(pending.IsCompleted);
        download.SetResult("public Double(x) = x * 2");
        var error = Assert.Single(Assert.IsType<RunResult.EvalFailure>(await pending).Errors);
        Assert.Equal(KatLangErrorCode.UnresolvedImplicitParams, error.Code);
        Assert.Equal(2, error.StartLine);
        Assert.Equal(5, error.StartColumn);
        Assert.Equal(9, error.EndColumn);
        Assert.Contains("Did you mean 'Lib.Double'?", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public async Task DeferredSuspendedModuleLoad_FinalizesTheSelectedBranchMemberOrigin()
    {
        const string definitions = "F(0) = 0\nF(n) = { Lib = load('https://katlang.org/g24.kat')\n"
            + "Use = Lib.Dubel(4)\nUse }\n";
        var download = new TaskCompletionSource<string>(TaskCreationOptions.RunContinuationsAsynchronously);
        var downloads = 0;
        var options = new RunOptions
        {
            DownloadCode = (_, _) =>
            {
                downloads++;
                return new ValueTask<string>(download.Task);
            },
        };
        Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(definitions + "F(0)", options));
        Assert.Equal(0, downloads);

        var pending = KatLangEngine.RunAsync(definitions + "F(1)", options);
        Assert.False(pending.IsCompleted);
        Assert.Equal(1, downloads);
        download.SetResult("public Double(x) = x * 2");
        var error = Assert.Single(Assert.IsType<RunResult.EvalFailure>(await pending).Errors);
        Assert.Equal(KatLangErrorCode.ArityMismatch, error.Code);
        Assert.Contains("was inferred at [3:11]", error.Message, StringComparison.Ordinal);
        Assert.Contains("Property 'Dubel' was not found on `Lib`", error.Message, StringComparison.Ordinal);
        Assert.Contains("Did you mean 'Lib.Double'?", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public async Task ImportedPropertyTypo_KeepsArityDemandAtTheLocalReference()
    {
        var result = await KatLangEngine.RunAsync("open 'https://katlang.org/g24.kat'\nUse + 1",
            new RunOptions { DownloadCode = (_, _) => ValueTask.FromResult("public Use = Math.Ceiling(2.1)") });
        var error = Assert.Single(Assert.IsType<RunResult.EvalFailure>(result).Errors);
        Assert.Equal(KatLangErrorCode.ArityMismatch, error.Code);
        Assert.Equal(2, error.StartLine);
        Assert.Equal(1, error.StartColumn);
        Assert.Contains("Did you mean 'Math.Ceil'?", error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public async Task ImportedBlockTypo_DoesNotPositionTheImportingDocumentAtModuleCoordinates()
    {
        var result = await KatLangEngine.RunAsync("P = { 1, load('https://katlang.org/g24.kat') }\nP",
            new RunOptions { DownloadCode = (_, _) => ValueTask.FromResult("Math.Ceiling(2.1)") });
        var error = Assert.Single(Assert.IsType<RunResult.EvalFailure>(result).Errors);
        Assert.Equal(KatLangErrorCode.UnresolvedImplicitParams, error.Code);
        Assert.Equal(1, error.StartLine);
        Assert.Equal(10, error.StartColumn);
        Assert.Contains("Did you mean 'Math.Ceil'?", error.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SharedFallbackLeaf_UsesItsFirstSemanticOccurrence(bool dotFirst)
    {
        var syntax = SourceProvenance.ParseSyntaxValidRoot(MathCeilingTypo);
        var dot = Assert.IsType<Expr.DotCall>(Assert.Single(syntax.Output));
        var sharedName = dot.EffectiveLexicalFallback;
        dot = dot with { LexicalFallback = sharedName };
        var root = syntax with { Output = dotFirst ? [dot, sharedName] : [sharedName, dot] };
        var detected = ParameterDetector.Detect(root);
        Assert.Empty(detected.Diagnostics);
        var note = Assert.Single(detected.Root.Parameters).InferredProvenance!;
        Assert.Equal(dotFirst, note.DotMemberOrigin is not null);
        Assert.Equal(dotFirst ? "Math.Ceil" : null, note.SuggestedName);
    }

    [Theory]
    [InlineData("v", "V", "Lib.V")]
    [InlineData("X", "V", null)]
    [InlineData("Ābale", "Ābele", "Lib.Ābele")]
    [InlineData("Membre", "Member", "Lib.Member")]
    public void MemberSuggestions_RespectShortNamesUnicodeAndTransposition(string typo, string member, string? expected)
        => Assert.Equal(expected, SingleNote(FailWithParity(
            $"Lib = {{ public {member} = 1 }}\nLib.{typo}").PlainError).SuggestedName);

    [Fact]
    public void TruncatedReceiverDescription_IsNotOfferedAsWritableQualification()
    {
        var receiver = new string('L', ExprNameRenderer.MaxRenderedNameLength + 1);
        var note = SingleNote(FailWithParity($"{receiver} = {{ public Double(x) = x }}\n{receiver}.Dubel(4)").PlainError);
        Assert.EndsWith(ExprNameRenderer.TruncationMarker, note.DotMemberOrigin!.ReceiverDescription, StringComparison.Ordinal);
        Assert.Equal("Double", note.SuggestedName);
    }

    [Fact]
    public void ReceiverAwareProvenance_IsInternalAndLeavesTheStructuredErrorUnchanged()
    {
        var assembly = typeof(ParameterDeclaration).Assembly;
        Assert.False(assembly.GetType("KatLang.DotMemberFallbackOrigin", throwOnError: true)!.IsPublic);

        var (_, error) = FailWithParity(MathCeilingTypo);
        var unresolved = Assert.IsType<EvalError.UnresolvedImplicitParams>(Innermost(error));
        Assert.DoesNotContain(
            typeof(EvalError.UnresolvedImplicitParams).GetProperties(System.Reflection.BindingFlags.Instance | System.Reflection.BindingFlags.Public),
            property => property.Name is "InferredImplicitParameters" or "DotMemberOrigin");

        // The public identity of the error is its parameter names alone.
        Assert.Equal(["Ceiling"], unresolved.ParamNames);
        Assert.Equal(KatLangErrorCode.UnresolvedImplicitParams, unresolved.Code);
    }
}
