namespace KatLang.Tests;

/// <summary>
/// Unresolved-name typo diagnostics for inferred implicit parameters.
///
/// <para>KatLang promotes unresolved identifiers to implicit parameters by
/// design, which used to erase the misspelled name from eventual
/// zero-argument/arity diagnostics ("Property 'Use' expects 1 parameter..."
/// with no trace of the typo that created the parameter). The detector now
/// records diagnostic-only <see cref="ImplicitParameterProvenance"/> — the
/// unresolved name, its first semantic source occurrence, and a conservative
/// near-miss suggestion computed against the SAME ownership-first lookup scope
/// the promotion decision used — and the evaluator's arity/unresolved-parameter
/// errors carry it through to rendering.</para>
///
/// <para>Everything here is diagnostic-only: these tests also pin that
/// resolution, inference (names, counts, order), and evaluation results are
/// UNCHANGED — a near-miss candidate never wins resolution.</para>
/// </summary>
public class ImplicitParameterDiagnosticsTests
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

    // ── 1. Structural/public property typo ─────────────────────────────────

    [Fact]
    public void StructuralPropertyTypo_SuggestsMemberName()
    {
        var (message, error) = FailWithParity(
            """
            M = { public Value = 42 }
            M.Valeu
            """);

        var unresolved = Assert.IsType<EvalError.UnresolvedImplicitParams>(Innermost(error));
        Assert.Equal(["Valeu"], unresolved.ParamNames);

        var note = SingleNote(error);
        Assert.Equal("Valeu", note.Name);
        Assert.Equal("Value", note.SuggestedName);
        Assert.NotNull(note.Span);
        Assert.Equal(2, note.Span!.StartLineNumber);

        Assert.Contains("'Valeu'", message, StringComparison.Ordinal);
        Assert.Contains("Did you mean 'Value'?", message, StringComparison.Ordinal);
    }

    // ── 2. Math member typo ────────────────────────────────────────────────

    [Fact]
    public void MathMemberTypo_SuggestsMathMember()
    {
        var (message, error) = FailWithParity("Math.Pie");

        var note = SingleNote(error);
        Assert.Equal("Pie", note.Name);
        Assert.Equal("Pi", note.SuggestedName);
        // The occurrence is the member identifier to the right of the dot.
        Assert.NotNull(note.Span);
        Assert.Equal(1, note.Span!.StartLineNumber);
        Assert.Equal(6, note.Span.StartColumn);

        Assert.Contains("Did you mean 'Pi'?", message, StringComparison.Ordinal);
    }

    // ── 3. Lexical dot-call fallback typo ──────────────────────────────────

    [Fact]
    public void BuiltinDotCallFallbackTypo_SuggestsBuiltinName()
    {
        var (message, error) = FailWithParity("range(1,5).fitler({x > 2})");

        var note = SingleNote(error);
        Assert.Equal("fitler", note.Name);
        Assert.Equal("filter", note.SuggestedName);

        Assert.Contains("Did you mean 'filter'?", message, StringComparison.Ordinal);
    }

    // ── 4. Case typo ───────────────────────────────────────────────────────

    [Fact]
    public void CaseTypo_SuggestsCaseCorrectedVisibleName()
    {
        var (message, error) = FailWithParity(
            """
            S = (1, 2, 3)
            S.Count
            """);

        var note = SingleNote(error);
        Assert.Equal("Count", note.Name);
        Assert.Equal("count", note.SuggestedName);

        Assert.Contains("Did you mean 'count'?", message, StringComparison.Ordinal);
    }

    // ── 5. Nested/open case: provenance survives to the eventual arity error ─

    private const string NestedOpenTypoSource =
        """
        Lib = { public Value = 42 }

        Use = {
          open Lib
          Valeu
        }

        Use
        """;

    [Fact]
    public void NestedOpenTypo_ArityErrorCarriesProvenanceAndSuggestion()
    {
        var (message, error) = FailWithParity(NestedOpenTypoSource);

        // The structured error is still the ordinary property arity mismatch —
        // enriched with provenance, not replaced by a new error kind.
        var contextual = Assert.IsType<EvalError.WithContext>(error);
        var propertyContext = Assert.IsType<PropertyEvaluationContext>(contextual.ErrorContext);
        Assert.Equal("Use", propertyContext.PropertyName);
        var arity = Assert.IsType<EvalError.ArityMismatch>(contextual.Inner);
        Assert.Equal(1, arity.Expected);
        Assert.Equal(0, arity.Actual);

        var note = SingleNote(error);
        Assert.Equal("Valeu", note.Name);
        Assert.Equal("Value", note.SuggestedName);
        Assert.NotNull(note.Span);
        Assert.Equal(5, note.Span!.StartLineNumber);
        Assert.Equal(3, note.Span.StartColumn);

        Assert.Equal(
            "Property 'Use' expects 1 parameter, but was called with 0 arguments.\n"
            + "An implicit parameter 'Valeu' was inferred at [5:3].\n"
            + "Did you mean 'Value'?",
            message);
    }

    [Fact]
    public async Task NestedOpenTypo_AsyncEngineMessageMatchesSync()
    {
        var syncFailure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(NestedOpenTypoSource));
        var asyncFailure = Assert.IsType<RunResult.EvalFailure>(await KatLangEngine.RunAsync(NestedOpenTypoSource));

        var syncError = Assert.Single(syncFailure.Errors);
        var asyncError = Assert.Single(asyncFailure.Errors);
        Assert.Equal(syncError.Message, asyncError.Message);
        Assert.Contains("An implicit parameter 'Valeu' was inferred at [5:3].", syncError.Message, StringComparison.Ordinal);
    }

    [Fact]
    public async Task LoadedModuleOpen_CarriesEligibleSuggestion()
    {
        const string url = "https://katlang.org/diagnostic-lib.kat";
        var parsed = await Parser.ParseAsync(
            $"open '{url}'\nValeu",
            new RunOptions
            {
                DownloadCode = (requested, _) => requested == url
                    ? ValueTask.FromResult("public Value = 42")
                    : ValueTask.FromException<string>(new InvalidOperationException("unexpected URL")),
            });

        Assert.False(parsed.HasErrors, string.Join(Environment.NewLine, parsed.Diagnostics.Select(static d => d.Message)));
        var result = Evaluator.Run(new Expr.AlgorithmExpr(parsed.Root));
        Assert.True(result.IsError);
        Assert.Equal("Value", SingleNote(result.Error).SuggestedName);
        Assert.Contains("Did you mean 'Value'?", KatLangError.FromEvalError(result.Error).Message, StringComparison.Ordinal);
    }

    [Fact]
    public void StandaloneParameterDetectorPath_FinalizesSuggestionEligibility()
    {
        // ParameterDetector.Detect is a standalone single-pass entry point
        // (internal since v0.8.187, reachable here through friend access). A
        // caller may evaluate its returned AST directly, without the full
        // pipeline's later PropertyExposureResolver; suggestions must agree
        // with the exposure values that direct evaluation actually observes.
        var syntax = Parser.ParseSyntax(
            """
            M = { public Value = 42 }
            M.Valeu
            """);
        Assert.False(syntax.HasErrors);

        var detected = ParameterDetector.Detect(syntax.Root);
        Assert.Empty(detected.Diagnostics);

        var result = Evaluator.Run(new Expr.AlgorithmExpr(detected.Root));
        Assert.True(result.IsError);
        Assert.Equal("Value", SingleNote(result.Error).SuggestedName);
        Assert.Contains(
            "Did you mean 'Value'?",
            KatLangError.FromEvalError(result.Error).Message,
            StringComparison.Ordinal);
    }

    // ── 6. Genuine intentional implicit parameters: no misleading suggestion ─

    [Fact]
    public void IntentionalImplicitParameters_NoNearMatch_EmitsNoSuggestion()
    {
        var (message, error) = FailWithParity("myAlpha + myBeta");

        var unresolved = Assert.IsType<EvalError.UnresolvedImplicitParams>(Innermost(error));
        Assert.Equal(["myAlpha", "myBeta"], unresolved.ParamNames);
        Assert.NotNull(unresolved.InferredImplicitParameters);
        Assert.All(unresolved.InferredImplicitParameters!, note => Assert.Null(note.SuggestedName));

        Assert.DoesNotContain("Did you mean", message, StringComparison.Ordinal);
    }

    [Fact]
    public void IntentionalZeroArgPropertyAccess_NoteIdentifiesOriginWithoutSuggestion()
    {
        var (message, error) = FailWithParity(
            """
            A = myInput
            A
            """);

        var note = SingleNote(error);
        Assert.Equal("myInput", note.Name);
        Assert.Null(note.SuggestedName);

        Assert.Equal(
            "Property 'A' expects 1 parameter, but was called with 0 arguments.\n"
            + "An implicit parameter 'myInput' was inferred at [1:5].",
            message);
    }

    // ── 7. Ambiguous/equally-close candidates: no arbitrary suggestion ─────

    [Fact]
    public void EquallyCloseCandidates_EmitNoSuggestion()
    {
        var (message, error) = FailWithParity(
            """
            Vault1 = 1
            Vault2 = 2
            Vault9
            """);

        var note = SingleNote(error);
        Assert.Equal("Vault9", note.Name);
        Assert.Null(note.SuggestedName);
        Assert.DoesNotContain("Did you mean", message, StringComparison.Ordinal);
    }

    // ── 8. Explicit parameter lists stay closed with their precise diagnostic ─

    [Fact]
    public void ExplicitParameterList_KeepsPreciseUndeclaredIdentifierDiagnostic()
    {
        var diagnostics = SourceProvenance.ExpectFrontEndError("F(alpha) = alfa + 1\nF(1)");

        var diagnostic = Assert.Single(diagnostics, d => d.Severity == DiagnosticSeverity.Error);
        Assert.Contains(
            "Identifier 'alfa' is used in an explicitly parameterized algorithm, but it is not declared in the parameter list.",
            diagnostic.Message,
            StringComparison.Ordinal);
        Assert.Equal(1, diagnostic.Span.StartLineNumber);
        Assert.Equal(12, diagnostic.Span.StartColumn);
        Assert.DoesNotContain("Did you mean", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ConditionalBranch_RemainsClosedAndDoesNotInferTypoParameter()
    {
        var parsed = SourceProvenance.ParseValid(
            """
            F(0) = Math.Pie
            F(x) = x
            F(0)
            """);

        var conditional = Assert.IsType<Algorithm.Conditional>(Assert.Single(parsed.Root.Properties).Value);
        Assert.All(conditional.Branches, branch => Assert.Empty(branch.Body.Parameters));

        var result = parsed.Evaluate();
        var unknown = Assert.IsType<EvalError.UnknownName>(Innermost(result.Error));
        Assert.Equal("Pie", unknown.Name);
        Assert.DoesNotContain("Did you mean", KatLangError.FromEvalError(result.Error).Message, StringComparison.Ordinal);
    }

    // ── 9. Dot candidates follow real member/fallback visibility rules ─────

    [Fact]
    public void DotMemberSuggestion_ReachesPrivateStructuralMember()
    {
        // Structural dot access deliberately ignores publicness, so a private
        // member is a legitimate dot-member candidate.
        var (message, error) = FailWithParity(
            """
            M = { Value = 42 }
            M.Valeu
            """);

        Assert.Equal("Value", SingleNote(error).SuggestedName);
        Assert.Contains("Did you mean 'Value'?", message, StringComparison.Ordinal);
    }

    [Fact]
    public void BareNameSuggestion_RespectsOpenVisibility()
    {
        // `open` exposes only public members: the private `Value` is NOT
        // visible in `Use`, so it must not be suggested for the bare `Valeu` —
        // but the provenance note itself still identifies the origin.
        var (message, error) = FailWithParity(
            """
            Lib = { Value = 42 }
            Use = {
              open Lib
              Valeu
            }
            Use
            """);

        var note = SingleNote(error);
        Assert.Equal("Valeu", note.Name);
        Assert.Null(note.SuggestedName);
        Assert.Contains("An implicit parameter 'Valeu' was inferred at [4:3].", message, StringComparison.Ordinal);
        Assert.DoesNotContain("Did you mean", message, StringComparison.Ordinal);
    }

    [Fact]
    public void CandidateBudgetExceeded_ConservativelyEmitsNoSuggestion()
    {
        var definitions = string.Join(
            '\n',
            Enumerable.Range(0, 513).Select(static index => $"Candidate{index} = {index}"));
        var (message, error) = FailWithParity($"{definitions}\nCanddate0");

        Assert.Null(SingleNote(error).SuggestedName);
        Assert.DoesNotContain("Did you mean", message, StringComparison.Ordinal);
    }

    // ── Mutation-campaign 2026-08-22: candidate-collection budget/dedup gaps ──
    // These pin TryCollectVisibleLexicalNames' CONSERVATIVE contract, which the
    // pre-campaign suite left unobserved: three surviving mutants (Stryker
    // 978/991/1009) changed candidate-collection outcomes without failing a test.

    /// <summary>
    /// Budget exhaustion must suppress the suggestion ENTIRELY, including an
    /// otherwise-available structural member candidate. Structural candidates are
    /// collected BEFORE the lexical sweep, so a mutant that reports budget failure
    /// as success (returning true with an empty name list instead of false) still
    /// has 'Value' in hand and would suggest it. The pre-existing budget test uses
    /// a BARE name, where candidates is empty either way and the two agree.
    /// </summary>
    [Fact]
    public void CandidateBudgetExceeded_SuppressesEvenAnAvailableStructuralSuggestion()
    {
        var definitions = string.Join(
            '\n',
            Enumerable.Range(0, 513).Select(static index => $"Candidate{index} = {index}"));
        var (message, error) = FailWithParity(
            $"{definitions}\nM = {{ public Value = 42 }}\nM.Valeu");

        Assert.Null(SingleNote(error).SuggestedName);
        Assert.DoesNotContain("Did you mean", message, StringComparison.Ordinal);
    }

    /// <summary>
    /// Same conservative rule when the budget is exhausted while sweeping an
    /// OPENED target's exported properties rather than direct lexical ones.
    /// </summary>
    [Fact]
    public void CandidateBudgetExceededThroughOpen_SuppressesEvenAnAvailableStructuralSuggestion()
    {
        var members = string.Join(
            '\n',
            Enumerable.Range(0, 513).Select(static index => $"  public Opened{index} = {index}"));
        var (message, error) = FailWithParity(
            $"open Lib\nLib = {{\n{members}\n}}\nM = {{ public Value = 42 }}\nM.Valeu");

        Assert.Null(SingleNote(error).SuggestedName);
        Assert.DoesNotContain("Did you mean", message, StringComparison.Ordinal);
    }

    /// <summary>
    /// A name visible at TWO scope levels is collected once; the repeat sighting is
    /// an ordinary skip, NOT budget exhaustion. A mutant that reports the duplicate
    /// as a collection failure silently suppresses every suggestion in any program
    /// where a name is shadowed — the common case this test pins.
    /// </summary>
    [Fact]
    public void NameVisibleAtTwoScopeLevels_StillYieldsSuggestion()
    {
        var (message, error) = FailWithParity(
            """
            Value = 1
            Wrapper = {
              Value = 2
              Valeu
            }
            Wrapper
            """);

        Assert.Equal("Value", SingleNote(error).SuggestedName);
        Assert.Contains("Did you mean 'Value'?", message, StringComparison.Ordinal);
    }

    [Fact]
    public void BareNameSuggestion_SuppressesAmbiguousOpenedCandidate()
    {
        // Correcting Valeu to Value would not resolve: the authoritative
        // ownership-first lookup returns both open providers and evaluation
        // reports AmbiguousOpen. A diagnostic must not present it confidently.
        var (message, error) = FailWithParity(
            """
            A = { public Value = 1 }
            B = { public Value = 2 }
            Use = {
              open A, B
              Valeu
            }
            Use
            """);

        Assert.Null(SingleNote(error).SuggestedName);
        Assert.DoesNotContain("Did you mean", message, StringComparison.Ordinal);

        var corrected = SourceProvenance.ParseValid(
            """
            A = { public Value = 1 }
            B = { public Value = 2 }
            Use = {
              open A, B
              Value
            }
            Use
            """).Evaluate();
        Assert.IsType<EvalError.AmbiguousOpen>(Innermost(corrected.Error));
    }

    [Fact]
    public void CapturedNameCandidate_SuppressesAmbiguousOpenShadow()
    {
        // Captured parameters normally qualify as nearby visible names, but
        // this exact spelling is shadowed by two opened non-builtin providers.
        // Parameter rewriting deliberately leaves it to lexical lookup, whose
        // real outcome is ambiguity.
        var (message, error) = FailWithParity(
            """
            Outer(Value) = {
              A = { public Value = 1 }
              B = { public Value = 2 }
              Use = {
                open A, B
                Valeu
              }
              Use
            }
            Outer(9)
            """);

        Assert.Null(SingleNote(error).SuggestedName);
        Assert.DoesNotContain("Did you mean", message, StringComparison.Ordinal);
    }

    [Fact]
    public void BareNameSuggestion_SuppressesMemberThatBecomesLocalOnly()
    {
        // Candidate collection precedes exposure analysis, but Value captures
        // Outer's seed and is therefore not exported through open in the final
        // program. The final exposure classification must veto the early
        // near-match rather than suggesting a spelling that still fails.
        var (message, error) = FailWithParity(
            """
            Outer(seed) = {
              Lib = { public Value = seed }
              Use = {
                open Lib
                Valeu
              }
              Use
            }
            Outer(1)
            """);

        Assert.Null(SingleNote(error).SuggestedName);
        Assert.DoesNotContain("Did you mean", message, StringComparison.Ordinal);

        var corrected = SourceProvenance.ParseValid(
            """
            Outer(seed) = {
              Lib = { public Value = seed }
              Use = {
                open Lib
                Value
              }
              Use
            }
            Outer(1)
            """).Evaluate();
        var unknown = Assert.IsType<EvalError.UnknownName>(Innermost(corrected.Error));
        Assert.Equal("Value", unknown.Name);
    }

    [Fact]
    public void DotMemberSuggestion_StructuralMemberOutranksEquallyCloseLexicalName()
    {
        // Both candidates are one edit away; structural-first dot resolution
        // makes the receiver's member the better-ranked suggestion.
        var (message, error) = FailWithParity(
            """
            M = { public Valxe = 1 }
            Valye = 2
            M.Value
            """);

        Assert.Equal("Valxe", SingleNote(error).SuggestedName);
        Assert.Contains("Did you mean 'Valxe'?", message, StringComparison.Ordinal);
    }

    // ── 10. Diagnostics-only: inference and evaluation are unchanged ───────

    [Fact]
    public void SuggestionNeverInfluencesResolution_SuppliedArgumentStillBindsParameter()
    {
        // With an argument supplied, `Valeu` binds that argument — never the
        // near-miss `Value` (42) the diagnostic would have suggested.
        var source =
            """
            Lib = { public Value = 42 }
            Use = {
              open Lib
              Valeu
            }
            Use(5)
            """;

        var provenance = SourceProvenance.ParseValid(source);

        var useProperty = Assert.Single(provenance.Root.Properties, p => p.Name == "Use");
        Assert.Equal(["Valeu"], useProperty.Value.Params);

        var result = provenance.Evaluate();
        Assert.False(result.IsError, $"expected success, got: {(result.IsError ? KatLangError.FromEvalError(result.Error).Message : null)}");
        Assert.Equal(5m, Assert.IsType<Result.Atom>(result.Value).Value);
    }

    [Fact]
    public void InferredSignatureOrderAndCountsAreUnchangedByProvenance()
    {
        // Dot fallback occurrence order (receiver, member, arguments) and the
        // inferred parameter count stay exactly as before; provenance is
        // metadata on the same declarations.
        var provenance = SourceProvenance.ParseValid("K = a.t(b)\n1");

        var kProperty = Assert.Single(provenance.Root.Properties, p => p.Name == "K");
        Assert.Equal(["a", "t", "b"], kProperty.Value.Params);
        Assert.All(
            kProperty.Value.Parameters,
            parameter =>
            {
                Assert.NotNull(parameter.InferredProvenance);
                Assert.Equal(parameter.Name, parameter.InferredProvenance!.Name);
            });
    }

    [Fact]
    public void DiagnosticMetadata_DoesNotExpandPublicAstOrErrorApiOrRecordIdentity()
    {
        var parsed = SourceProvenance.ParseValid("A = typo\n1");
        var algorithm = Assert.Single(parsed.Root.Properties).Value;
        var parameter = Assert.Single(algorithm.Parameters);
        var pattern = Assert.IsType<CaptureParameterPattern>(
            Assert.Single(algorithm.ParameterPatterns));
        Assert.NotNull(parameter.InferredProvenance);
        Assert.NotNull(pattern.InferredProvenance);

        // The public AST identity remains the same three semantic/source
        // fields it had before diagnostic provenance existed.
        Assert.Equal(new ParameterDeclaration("typo"), parameter);
        Assert.Equal(new CaptureParameterPattern("typo"), pattern);

        var provenance = parameter.InferredProvenance!;
        var enrichedError = new EvalError.ArityMismatch(1, 0)
        {
            InferredImplicitParameters = [provenance],
        };
        Assert.Equal(new EvalError.ArityMismatch(1, 0), enrichedError);

        // `with` cloning is common throughout the evaluator/front end; the
        // side metadata follows clones even though equality ignores it.
        Assert.Same(provenance, (parameter with { }).InferredProvenance);
        Assert.Same(provenance, (pattern with { }).InferredProvenance);
        Assert.Same(provenance, Assert.Single((enrichedError with { Span = new SourceSpan(1, 1, 1, 1) }).InferredImplicitParameters!));

        var assembly = typeof(ParameterDeclaration).Assembly;
        Assert.False(assembly.GetType("KatLang.ImplicitParameterProvenance", throwOnError: true)!.IsPublic);
        Assert.DoesNotContain(
            typeof(ParameterDeclaration).GetProperties(System.Reflection.BindingFlags.Instance | System.Reflection.BindingFlags.Public),
            property => property.Name == "InferredProvenance");
        Assert.DoesNotContain(
            typeof(CaptureParameterPattern).GetProperties(System.Reflection.BindingFlags.Instance | System.Reflection.BindingFlags.Public),
            property => property.Name == "InferredProvenance");
        Assert.DoesNotContain(
            typeof(EvalError.ArityMismatch).GetProperties(System.Reflection.BindingFlags.Instance | System.Reflection.BindingFlags.Public),
            property => property.Name == "InferredImplicitParameters");
    }

    // ── Wrong-argument-count calls carry the same provenance ───────────────

    [Fact]
    public void WrongArgumentCountCall_CarriesProvenanceSuggestion()
    {
        var (message, _) = FailWithParity(
            """
            Lib = { public Value = 42 }
            Use = {
              open Lib
              Valeu
            }
            Use(1, 2)
            """);

        Assert.Equal(
            "Callable `Use(Valeu)` expects 1 argument, but was called with 2 arguments.\n"
            + "An implicit parameter 'Valeu' was inferred at [4:3].\n"
            + "Did you mean 'Value'?",
            message);
    }

    [Fact]
    public void WrongArgumentCountCall_WithoutSuggestion_KeepsSignatureMessageClean()
    {
        // The signature already displays the (intentional) inferred parameter
        // names; without a near-miss there is nothing to add.
        var (message, _) = FailWithParity(
            """
            Add = myLeft + myRight
            Add(1)
            """);

        Assert.Equal("Callable `Add(myLeft, myRight)` expects 2 arguments, but was called with 1 argument.", message);
    }

    [Fact]
    public async Task CallbackBindingArity_CarriesProvenanceAcrossSyncCountedAndAsyncTwin()
    {
        var source =
            """
            M = { public Value = 42 }
            F = item + M.Valeu
            map((1, 2), F)
            """;

        var (message, error) = FailWithParity(source);
        var callbackArity = Assert.IsType<EvalError.ArityMismatch>(Innermost(error));
        var callbackTypo = Assert.Single(callbackArity.InferredImplicitParameters!, note => note.Name == "Valeu");
        Assert.Equal("Value", callbackTypo.SuggestedName);
        Assert.Contains("Did you mean 'Value'?", message, StringComparison.Ordinal);

        var asyncResult = await KatLang.Tests.AsyncEvaluation.AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedAsync(
                Program(source),
                new KatLang.Tests.AsyncEvaluation.PassThroughAsyncZeroArgPropertyResultCache()));
        Assert.True(asyncResult.IsError);
        Assert.Equal(message, KatLangError.FromEvalError(asyncResult.Error).Message);
    }

    [Fact]
    public void LoopStateBindingArity_CarriesProvenance()
    {
        var (message, error) = FailWithParity(
            """
            M = { public Value = 42 }
            Step = state + M.Valeu
            repeat(Step, 1, 0)
            """);

        var loopArity = Assert.IsType<EvalError.ArityMismatch>(Innermost(error));
        var loopTypo = Assert.Single(loopArity.InferredImplicitParameters!, note => note.Name == "Valeu");
        Assert.Equal("Value", loopTypo.SuggestedName);
        Assert.Contains("Did you mean 'Value'?", message, StringComparison.Ordinal);
    }

    // ── Multiple typos are attributed individually ─────────────────────────

    [Fact]
    public void MultipleTypos_SuggestionsAttributePerName()
    {
        var (message, _) = FailWithParity(
            """
            M = { public Value = 42 }
            M.Valeu + Math.Pie
            """);

        Assert.Contains("Did you mean 'Value' instead of 'Valeu'?", message, StringComparison.Ordinal);
        Assert.Contains("Did you mean 'Pi' instead of 'Pie'?", message, StringComparison.Ordinal);
    }

    // ── Provenance survives transitive parameter lifting ───────────────────

    [Fact]
    public void LiftedParameter_KeepsOriginalProvenance()
    {
        // ImplicitArgumentResolver lifts Use's inferred `Valeu` through Bridge
        // and then into Helper; the eventual arity error on Helper must still
        // point at the ORIGINAL occurrence inside Use.
        var (message, error) = FailWithParity(
            """
            Lib = { public Value = 42 }
            Use = {
              open Lib
              Valeu
            }
            Bridge = Use + 1
            Helper = Bridge + 1
            Helper
            """);

        var note = SingleNote(error);
        Assert.Equal("Valeu", note.Name);
        Assert.Equal("Value", note.SuggestedName);
        Assert.NotNull(note.Span);
        Assert.Equal(4, note.Span!.StartLineNumber);
        Assert.Equal(3, note.Span.StartColumn);

        Assert.Equal(
            "Property 'Helper' expects 1 parameter, but was called with 0 arguments.\n"
            + "An implicit parameter 'Valeu' was inferred at [4:3].\n"
            + "Did you mean 'Value'?",
            message);
    }

    // ── Suggestion distance basics (internal engine sanity) ────────────────

    [Theory]
    [InlineData("Valeu", "Value", 1)] // adjacent transposition
    [InlineData("Pie", "Pi", 1)]      // deletion
    [InlineData("fitler", "filter", 1)]
    [InlineData("Count", "count", 1)] // case substitution (case-insensitive rule short-circuits before this)
    [InlineData("alfa", "alpha", 2)]
    public void OptimalStringAlignmentDistance_MatchesExpected(string a, string b, int expected)
        => Assert.Equal(expected, NameSuggestions.OptimalStringAlignmentDistance(a, b));
// Pins first-occurrence provenance when ONE inferred name occurs TWICE inside a single
// node -- a shape no pre-campaign test had. NOTE: the span these assert comes from the
// detector's RecordFirstOccurrence recorder, NOT from FindResolveSpan; the `??` chains
// there (mutants 1117/1127) are a FALLBACK used only when no recorder ran, and remain
// UNPINNED by these tests.

    [Fact]
    public void ImplicitParameterProvenance_TakesFirstOccurrenceAcrossBinaryOperands()
    {
        // `xx` occurs on BOTH operands; provenance must point at the FIRST.
        var (_, error) = FailWithParity("K = xx + xx\nK");

        var note = SingleNote(error);
        Assert.Equal("xx", note.Name);
        Assert.NotNull(note.Span);
        Assert.Equal(1, note.Span!.StartLineNumber);
        Assert.Equal(5, note.Span!.StartColumn);
    }

    [Fact]
    public void ImplicitParameterProvenance_TakesCalleeOccurrenceBeforeArgument()
    {
        // `xx` is both the callee and its own argument; the callee occurrence is first.
        var (_, error) = FailWithParity("K = xx(xx)\nK");

        var note = SingleNote(error);
        Assert.Equal("xx", note.Name);
        Assert.NotNull(note.Span);
        Assert.Equal(5, note.Span!.StartColumn);
    }
}
