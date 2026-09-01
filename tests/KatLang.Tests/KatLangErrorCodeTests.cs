using System.Reflection;

namespace KatLang.Tests;

/// <summary>
/// M5 structured error identity at the engine/host boundary: the authoritative
/// <see cref="EvalError"/> → <see cref="KatLangErrorCode"/> mapping is
/// mechanically exhaustive, <see cref="KatLangError"/> preserves the original
/// structured error and exposes its stable code, resource-limit classification
/// is public and structural, and representative <see cref="RunResult"/>
/// consumers can classify every failure kind without inspecting message text.
/// </summary>
public class KatLangErrorCodeTests
{
    // ── The authoritative variant sample table ──────────────────────────────

    /// <summary>
    /// One hand-written sample instance per concrete <see cref="EvalError"/>
    /// variant, beside its expected facade code and resource-limit verdict.
    /// <see cref="EveryConcreteEvalErrorVariant_IsCoveredByTheSampleTable"/>
    /// keeps this table reflection-complete, so a future variant cannot ship
    /// without an explicit mapping decision here.
    /// </summary>
    private static readonly IReadOnlyDictionary<Type, (EvalError Sample, KatLangErrorCode ExpectedCode, bool IsResourceLimit)> VariantSamples =
        new Dictionary<Type, (EvalError, KatLangErrorCode, bool)>
        {
            [typeof(EvalError.UnknownName)] = (new EvalError.UnknownName("x"), KatLangErrorCode.UnknownName, false),
            [typeof(EvalError.UnknownProperty)] = (new EvalError.UnknownProperty("Obj", "P"), KatLangErrorCode.UnknownProperty, false),
            [typeof(EvalError.NotPublicProperty)] = (new EvalError.NotPublicProperty("Obj", "P"), KatLangErrorCode.NotPublicProperty, false),
            [typeof(EvalError.LocalOnlyProperty)] = (
                new EvalError.LocalOnlyProperty("Obj", "P", PropertyExposure.LocalOnlyCapturedAncestorParameters),
                KatLangErrorCode.LocalOnlyProperty,
                false),
            [typeof(EvalError.NotAnAlgorithm)] = (new EvalError.NotAnAlgorithm("desc"), KatLangErrorCode.NotAnAlgorithm, false),
            [typeof(EvalError.IllegalInOpen)] = (new EvalError.IllegalInOpen("reason"), KatLangErrorCode.IllegalInOpen, false),
            [typeof(EvalError.BadOpenForm)] = (new EvalError.BadOpenForm("reason"), KatLangErrorCode.BadOpenForm, false),
            [typeof(EvalError.IllegalInEval)] = (new EvalError.IllegalInEval("reason"), KatLangErrorCode.IllegalInEval, false),
            [typeof(EvalError.AmbiguousOpen)] = (new EvalError.AmbiguousOpen("x", ["A", "B"]), KatLangErrorCode.AmbiguousOpen, false),
            [typeof(EvalError.ArityMismatch)] = (new EvalError.ArityMismatch(2, 3), KatLangErrorCode.ArityMismatch, false),
            [typeof(EvalError.VariadicArityMismatch)] = (
                new EvalError.VariadicArityMismatch("F", 2, 1), KatLangErrorCode.ArityMismatch, false),
            [typeof(EvalError.BadArity)] = (new EvalError.BadArity(), KatLangErrorCode.ArityMismatch, false),
            [typeof(EvalError.TypeMismatch)] = (new EvalError.TypeMismatch("msg"), KatLangErrorCode.TypeMismatch, false),
            [typeof(EvalError.BadIndex)] = (new EvalError.BadIndex(), KatLangErrorCode.BadIndex, false),
            [typeof(EvalError.DivByZero)] = (new EvalError.DivByZero(), KatLangErrorCode.DivisionByZero, false),
            [typeof(EvalError.NoMatchingBranch)] = (new EvalError.NoMatchingBranch("F"), KatLangErrorCode.NoMatchingBranch, false),
            [typeof(EvalError.BranchArityMismatch)] = (
                new EvalError.BranchArityMismatch("F", 1, 2), KatLangErrorCode.BranchArityMismatch, false),
            [typeof(EvalError.BranchOutputArityMismatch)] = (
                new EvalError.BranchOutputArityMismatch("F", 1, 2), KatLangErrorCode.BranchOutputArityMismatch, false),
            [typeof(EvalError.DuplicateProperty)] = (new EvalError.DuplicateProperty("A"), KatLangErrorCode.DuplicateProperty, false),
            [typeof(EvalError.DuplicateBranchPattern)] = (
                new EvalError.DuplicateBranchPattern(), KatLangErrorCode.DuplicateBranchPattern, false),
            [typeof(EvalError.ExplicitParametersRequireOutput)] = (
                new EvalError.ExplicitParametersRequireOutput(), KatLangErrorCode.ExplicitParametersRequireOutput, false),
            [typeof(EvalError.MissingOutput)] = (new EvalError.MissingOutput(), KatLangErrorCode.MissingOutput, false),
            [typeof(EvalError.SpreadMissingOutput)] = (new EvalError.SpreadMissingOutput(), KatLangErrorCode.SpreadMissingOutput, false),
            [typeof(EvalError.UnresolvedImplicitParams)] = (
                new EvalError.UnresolvedImplicitParams(["x"]), KatLangErrorCode.UnresolvedImplicitParams, false),
            [typeof(EvalError.EvaluationDepthExceeded)] = (
                new EvalError.EvaluationDepthExceeded(10), KatLangErrorCode.EvaluationDepthExceeded, true),
            [typeof(EvalError.EvaluationStepLimitExceeded)] = (
                new EvalError.EvaluationStepLimitExceeded(10), KatLangErrorCode.EvaluationStepLimitExceeded, true),
            [typeof(EvalError.CollectionSizeLimitExceeded)] = (
                new EvalError.CollectionSizeLimitExceeded(10, 11), KatLangErrorCode.CollectionSizeLimitExceeded, true),
            [typeof(EvalError.MaterializationLimitExceeded)] = (
                new EvalError.MaterializationLimitExceeded(10), KatLangErrorCode.MaterializationLimitExceeded, true),
            [typeof(EvalError.StringSizeLimitExceeded)] = (
                new EvalError.StringSizeLimitExceeded(10, 11), KatLangErrorCode.StringSizeLimitExceeded, true),
            [typeof(EvalError.StringMaterializationLimitExceeded)] = (
                new EvalError.StringMaterializationLimitExceeded(10), KatLangErrorCode.StringMaterializationLimitExceeded, true),
            [typeof(EvalError.DisplayLengthLimitExceeded)] = (
                new EvalError.DisplayLengthLimitExceeded(10), KatLangErrorCode.DisplayLengthLimitExceeded, true),
            [typeof(EvalError.EvaluationStackExhausted)] = (
                new EvalError.EvaluationStackExhausted(), KatLangErrorCode.EvaluationStackExhausted, true),
            [typeof(EvalError.AstDepthLimitExceeded)] = (
                new EvalError.AstDepthLimitExceeded(10), KatLangErrorCode.AstDepthLimitExceeded, true),
            [typeof(EvalError.AstCycleDetected)] = (new EvalError.AstCycleDetected(), KatLangErrorCode.AstCycleDetected, false),
            // The contextual wrapper resolves to its inner error's family; its
            // dedicated behavior is pinned by the WithContext tests below.
            [typeof(EvalError.WithContext)] = (
                new EvalError.WithContext(new CallContext("F"), new EvalError.UnknownName("x")),
                KatLangErrorCode.UnknownName,
                false),
        };

    [Fact]
    public void EveryConcreteEvalErrorVariant_IsCoveredByTheSampleTable()
    {
        var concreteVariants = typeof(EvalError).Assembly.GetTypes()
            .Where(t => t.IsAssignableTo(typeof(EvalError)) && !t.IsAbstract)
            .ToHashSet();

        Assert.NotEmpty(concreteVariants);

        var missing = concreteVariants.Except(VariantSamples.Keys).Select(t => t.Name).Order().ToList();
        Assert.True(missing.Count == 0,
            "EvalError variants without an explicit KatLangErrorCode mapping decision in the sample table: "
            + string.Join(", ", missing)
            + ". Add the variant to EvalError.Code and to this table in the same change.");

        var stale = VariantSamples.Keys.Except(concreteVariants).Select(t => t.Name).Order().ToList();
        Assert.True(stale.Count == 0, "Sample table entries for non-existent variants: " + string.Join(", ", stale));

        Assert.All(VariantSamples, entry => Assert.IsType(entry.Key, entry.Value.Sample));
    }

    [Fact]
    public void EveryVariant_MapsToItsFamilyCode_AndNeverUnspecified()
    {
        Assert.All(VariantSamples.Values, entry =>
        {
            Assert.Equal(entry.ExpectedCode, entry.Sample.Code);
            Assert.NotEqual(KatLangErrorCode.Unspecified, entry.Sample.Code);
        });
    }

    [Fact]
    public void WithContext_ResolvesToTheUnderlyingFamily_ThroughNestedWrappers()
    {
        var inner = new EvalError.EvaluationStepLimitExceeded(100);
        var wrapped = new EvalError.WithContext(
            new PropertyEvaluationContext("A"),
            new EvalError.WithContext(new CallContext("F"), inner));

        Assert.Equal(KatLangErrorCode.EvaluationStepLimitExceeded, wrapped.Code);

        var textWrapped = new EvalError.WithContext("while evaluating something", new EvalError.DivByZero());
        Assert.Equal(KatLangErrorCode.DivisionByZero, textWrapped.Code);
    }

    // ── KatLangError projection ─────────────────────────────────────────────

    [Fact]
    public void FromEvalError_PreservesTheOriginalStructuredError_ByReference()
    {
        var direct = new EvalError.DivByZero { Span = new SourceSpan(3, 2, 3, 5) };
        Assert.Same(direct, KatLangError.FromEvalError(direct).Source);

        // Context wrappers are preserved whole: Source keeps the richer
        // context while Code resolves to the underlying family.
        var wrapped = new EvalError.WithContext(new CallContext("F"), new EvalError.ArityMismatch(2, 3));
        var projected = KatLangError.FromEvalError(wrapped);
        Assert.Same(wrapped, projected.Source);
        Assert.Equal(KatLangErrorCode.ArityMismatch, projected.Code);
    }

    [Theory]
    [InlineData("open")]
    [InlineData("div")]
    public void FromEvalError_KeywordShapedHostNamesKeepTheBarePropertyDiagnostic(string name)
    {
        // A host-built AST can carry a keyword-shaped property description even
        // though source cannot spell that declaration. IsSimpleIdentifier is a
        // display-shape test, not a second source-validity gate; consolidation
        // must preserve the established, quoted "Property 'name'" wording.
        var error = new EvalError.WithContext(new CallContext(name), new EvalError.ArityMismatch(1, 0));

        Assert.Equal(
            $"Property '{name}' expects 1 parameter, but was called with 0 arguments.",
            KatLangError.FromEvalError(error).Message);
    }

    [Fact]
    public void FromEvalError_ProducesTheStableCode_ForEveryVariant()
    {
        Assert.All(VariantSamples.Values, entry =>
        {
            var projected = KatLangError.FromEvalError(entry.Sample);
            Assert.Equal(entry.ExpectedCode, projected.Code);
            Assert.Same(entry.Sample, projected.Source);
        });
    }

    [Fact]
    public void FromDiagnostic_MapsEveryDeclaredDiagnosticCode_NamePreserving()
    {
        // The DiagnosticCode → KatLangErrorCode mapping is name-preserving and
        // total over declared members: this walks the enum itself, so adding a
        // DiagnosticCode family without extending the facade mapping fails
        // here mechanically.
        foreach (var diagnosticCode in Enum.GetValues<DiagnosticCode>())
        {
            var diagnostic = new Diagnostic("m", DiagnosticSeverity.Error, new SourceSpan(1, 1, 1, 1))
            {
                Code = diagnosticCode,
            };
            var projected = KatLangError.FromDiagnostic(diagnostic);

            Assert.Null(projected.Source);

            if (diagnosticCode == DiagnosticCode.Unspecified)
            {
                Assert.Equal(KatLangErrorCode.Unspecified, projected.Code);
                continue;
            }

            Assert.True(Enum.TryParse<KatLangErrorCode>(diagnosticCode.ToString(), out var sameName),
                $"KatLangErrorCode has no member named {diagnosticCode}.");
            Assert.Equal(sameName, projected.Code);
            Assert.NotEqual(KatLangErrorCode.Unspecified, projected.Code);
        }
    }

    [Fact]
    public void FromDiagnostic_ExternallyConstructedDiagnostics_KeepTheExplicitUnspecifiedState()
    {
        // The legacy/compatibility path: a host-built diagnostic without a code
        // projects to the explicit Unspecified state — including an undeclared
        // numeric value smuggled in by cast.
        var legacy = KatLangError.FromDiagnostic(
            new Diagnostic("legacy", DiagnosticSeverity.Error, new SourceSpan(1, 1, 1, 1)));
        Assert.Equal(KatLangErrorCode.Unspecified, legacy.Code);
        Assert.Null(legacy.Source);
        Assert.False(legacy.IsResourceLimit);

        var undeclared = KatLangError.FromDiagnostic(
            new Diagnostic("cast", DiagnosticSeverity.Error, new SourceSpan(1, 1, 1, 1))
            {
                Code = (DiagnosticCode)9999,
            });
        Assert.Equal(KatLangErrorCode.Unspecified, undeclared.Code);
    }

    [Fact]
    public void EquivalentOpenFormFailures_ShareOneFacadeFamilyAcrossPhases()
    {
        var parseFailure = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run("open 5\n1"));
        var parseError = Assert.Single(parseFailure.Errors);
        Assert.Equal(KatLangErrorCode.BadOpenForm, parseError.Code);

        var evaluationError = KatLangError.FromEvalError(new EvalError.BadOpenForm("number: 5"));
        Assert.Equal(KatLangErrorCode.BadOpenForm, evaluationError.Code);

        Assert.DoesNotContain(
            Enum.GetNames<KatLangErrorCode>(),
            static name => string.Equals(name, "InvalidOpenForm", StringComparison.Ordinal));
    }

    // ── Resource-limit classification ───────────────────────────────────────

    [Fact]
    public void IsResourceLimit_CoversExactlyTheResourceLimitFamilies_AlsoThroughWrappers()
    {
        foreach (var entry in VariantSamples.Values)
        {
            Assert.Equal(entry.IsResourceLimit, entry.Sample.IsResourceLimit);
            Assert.Equal(entry.IsResourceLimit, KatLangError.FromEvalError(entry.Sample).IsResourceLimit);

            var wrapped = new EvalError.WithContext(new CallContext("F"), entry.Sample);
            Assert.Equal(entry.IsResourceLimit, wrapped.IsResourceLimit);
            Assert.Equal(entry.IsResourceLimit, KatLangError.FromEvalError(wrapped).IsResourceLimit);
        }
    }

    [Fact]
    public void IsResourceLimit_ClassifiesNineVariants_AndNoDiagnosticOriginError()
    {
        // The classified set is unchanged from the pre-M5 internal classifier:
        // nine evaluation resource-limit variants; a structural cycle is
        // malformed input, front-end source-processing limits are diagnostics
        // (never evaluation outcomes), and cancellation throws
        // OperationCanceledException instead of producing an error value.
        Assert.Equal(9, VariantSamples.Values.Count(entry => entry.IsResourceLimit));
        Assert.False(new EvalError.AstCycleDetected().IsResourceLimit);

        var sourceLimitDiagnostic = KatLangError.FromDiagnostic(
            SourceProcessingDiagnostics.SourceLengthExceeded(10, 5));
        Assert.Equal(KatLangErrorCode.SourceLengthExceeded, sourceLimitDiagnostic.Code);
        Assert.False(sourceLimitDiagnostic.IsResourceLimit);
    }

    // ── RunResult consumers classify without reading Message ────────────────

    [Fact]
    public void RunResultConsumers_ClassifyEveryFailureKind_WithoutInspectingMessage()
    {
        var parseFailure = Assert.IsType<RunResult.ParseFailure>(KatLangEngine.Run("1 ; 2"));
        var parseError = Assert.Single(parseFailure.Errors);
        Assert.Equal(KatLangErrorCode.UnsupportedSemicolon, parseError.Code);
        Assert.Null(parseError.Source);
        Assert.False(parseError.IsResourceLimit);

        var evalFailure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run("1 / 0"));
        var evalError = Assert.Single(evalFailure.Errors);
        Assert.Equal(KatLangErrorCode.DivisionByZero, evalError.Code);
        Assert.NotNull(evalError.Source);
        Assert.False(evalError.IsResourceLimit);

        var limitFailure = Assert.IsType<RunResult.EvalFailure>(KatLangEngine.Run(
            "F(n) = F(n + 1)\nF(1)",
            new RunOptions { EvaluationLimits = new EvaluationLimits { MaxSteps = 8 } }));
        var limitError = Assert.Single(limitFailure.Errors);
        Assert.Equal(KatLangErrorCode.EvaluationStepLimitExceeded, limitError.Code);
        Assert.True(limitError.IsResourceLimit);

        var loadFailure = Assert.IsType<RunResult.ParseFailure>(
            KatLangEngine.Run("open 'https://katlang.org/lib.kat'\n1"));
        Assert.Contains(loadFailure.Errors, e => e.Code == KatLangErrorCode.LoadElaborationUnavailable);

        var noOutput = Assert.IsType<RunResult.NoProgramOutput>(KatLangEngine.Run("A = 1"));
        Assert.Equal(KatLangErrorCode.MissingOutput, noOutput.Diagnostic.Code);
        Assert.NotNull(noOutput.Diagnostic.Source);
    }

    [Fact]
    public async Task AsyncAndSyncRuns_ProjectIdenticalStructuredClassification()
    {
        var programs = new (string Source, RunOptions? Options)[]
        {
            ("1 ; 2", null),
            ("1 / 0", null),
            ("F(n) = F(n + 1)\nF(1)", new RunOptions { EvaluationLimits = new EvaluationLimits { MaxSteps = 8 } }),
            ("open 'https://katlang.org/lib.kat'\n1", null),
        };

        foreach (var (source, options) in programs)
        {
            var sync = KatLangEngine.Run(source, options);
            var async = await KatLangEngine.RunAsync(source, options);

            static string Describe(KatLangError error)
                => $"{error.Code}|limit={error.IsResourceLimit}|source={error.Source?.GetType().Name ?? "null"}";

            static string Classify(RunResult result)
                => result switch
                {
                    RunResult.ParseFailure p => "parse: " + string.Join("; ", p.Errors.Select(Describe)),
                    RunResult.EvalFailure e => "eval: " + string.Join("; ", e.Errors.Select(Describe)),
                    RunResult.NoProgramOutput n => "noOutput: " + Describe(n.Diagnostic),
                    _ => "success",
                };

            Assert.Equal(Classify(sync), Classify(async));
        }
    }

    // ── Enum stability and public API shape ─────────────────────────────────

    [Fact]
    public void DiagnosticCodeValues_AreStable()
    {
        // Names and numeric values are public contract: append-only. This pin
        // fails on any renumbering, rename, or removal; extend it when
        // appending a new family.
        var expected = new Dictionary<string, int>
        {
            ["Unspecified"] = 0,
            ["UnexpectedCharacter"] = 1,
            ["UnterminatedStringLiteral"] = 2,
            ["NumberLiteralTooLarge"] = 3,
            ["UnexpectedToken"] = 4,
            ["UnsupportedSemicolon"] = 5,
            ["NestingTooDeep"] = 6,
            ["ExpressionChainTooDeep"] = 7,
            ["DuplicateProperty"] = 8,
            ["DeclarationInParentheses"] = 9,
            ["InvalidOpenDeclaration"] = 10,
            ["InvalidOpenTargetList"] = 11,
            ["BadOpenForm"] = 12,
            ["DuplicateBranchPattern"] = 13,
            ["BranchArityMismatch"] = 14,
            ["BranchOutputArityMismatch"] = 15,
            ["ClauseVisibilityMismatch"] = 16,
            ["InvalidGraceMarker"] = 17,
            ["InvalidCollectMarker"] = 18,
            ["InvalidCollectingBinding"] = 19,
            ["MisplacedSpread"] = 20,
            ["ArityMismatch"] = 21,
            ["ExplicitParametersRequireOutput"] = 22,
            ["UndeclaredIdentifier"] = 23,
            ["AstDepthLimitExceeded"] = 24,
            ["AstCycleDetected"] = 25,
            ["SourceLengthExceeded"] = 26,
            ["AggregateSourceLengthExceeded"] = 27,
            ["ModuleImportDepthExceeded"] = 28,
            ["ModuleCountExceeded"] = 29,
            ["ModuleNestingTooDeep"] = 30,
            ["ModuleElaborationStackExhausted"] = 31,
            ["InvalidLoadDirective"] = 32,
            ["InvalidLoadUrl"] = 33,
            ["LoadCycle"] = 34,
            ["LoadFetchFailed"] = 35,
            ["InvalidLoadedSource"] = 36,
            ["LoadElaborationUnavailable"] = 37,
            ["InternalError"] = 38,
        };

        var actual = Enum.GetValues<DiagnosticCode>().ToDictionary(v => v.ToString(), v => (int)v);
        Assert.Equal(expected, actual);
    }

    [Fact]
    public void KatLangErrorCodeValues_AreStable()
    {
        var expected = new Dictionary<string, int>
        {
            ["Unspecified"] = 0,
            ["UnknownName"] = 1,
            ["UnknownProperty"] = 2,
            ["NotPublicProperty"] = 3,
            ["LocalOnlyProperty"] = 4,
            ["NotAnAlgorithm"] = 5,
            ["IllegalInOpen"] = 6,
            ["BadOpenForm"] = 7,
            ["IllegalInEval"] = 8,
            ["AmbiguousOpen"] = 9,
            ["ArityMismatch"] = 10,
            ["TypeMismatch"] = 11,
            ["BadIndex"] = 12,
            ["DivisionByZero"] = 13,
            ["NoMatchingBranch"] = 14,
            ["BranchArityMismatch"] = 15,
            ["BranchOutputArityMismatch"] = 16,
            ["DuplicateProperty"] = 17,
            ["DuplicateBranchPattern"] = 18,
            ["ExplicitParametersRequireOutput"] = 19,
            ["MissingOutput"] = 20,
            ["SpreadMissingOutput"] = 21,
            ["UnresolvedImplicitParams"] = 22,
            ["EvaluationDepthExceeded"] = 23,
            ["EvaluationStepLimitExceeded"] = 24,
            ["CollectionSizeLimitExceeded"] = 25,
            ["MaterializationLimitExceeded"] = 26,
            ["StringSizeLimitExceeded"] = 27,
            ["StringMaterializationLimitExceeded"] = 28,
            ["DisplayLengthLimitExceeded"] = 29,
            ["EvaluationStackExhausted"] = 30,
            ["AstDepthLimitExceeded"] = 31,
            ["AstCycleDetected"] = 32,
            ["UnexpectedCharacter"] = 33,
            ["UnterminatedStringLiteral"] = 34,
            ["NumberLiteralTooLarge"] = 35,
            ["UnexpectedToken"] = 36,
            ["UnsupportedSemicolon"] = 37,
            ["NestingTooDeep"] = 38,
            ["ExpressionChainTooDeep"] = 39,
            ["DeclarationInParentheses"] = 40,
            ["InvalidOpenDeclaration"] = 41,
            ["InvalidOpenTargetList"] = 42,
            ["ClauseVisibilityMismatch"] = 43,
            ["InvalidGraceMarker"] = 44,
            ["InvalidCollectMarker"] = 45,
            ["InvalidCollectingBinding"] = 46,
            ["MisplacedSpread"] = 47,
            ["UndeclaredIdentifier"] = 48,
            ["SourceLengthExceeded"] = 49,
            ["AggregateSourceLengthExceeded"] = 50,
            ["ModuleImportDepthExceeded"] = 51,
            ["ModuleCountExceeded"] = 52,
            ["ModuleNestingTooDeep"] = 53,
            ["ModuleElaborationStackExhausted"] = 54,
            ["InvalidLoadDirective"] = 55,
            ["InvalidLoadUrl"] = 56,
            ["LoadCycle"] = 57,
            ["LoadFetchFailed"] = 58,
            ["InvalidLoadedSource"] = 59,
            ["LoadElaborationUnavailable"] = 60,
            ["InternalError"] = 61,
        };

        var actual = Enum.GetValues<KatLangErrorCode>().ToDictionary(v => v.ToString(), v => (int)v);
        Assert.Equal(expected, actual);
    }

    [Fact]
    public void PublicApiShape_NewMembersPresent_ExistingShapesIntact()
    {
        // New public surface.
        Assert.True(typeof(DiagnosticCode).IsPublic && typeof(DiagnosticCode).IsEnum);
        Assert.True(typeof(KatLangErrorCode).IsPublic && typeof(KatLangErrorCode).IsEnum);
        Assert.Equal(typeof(int), Enum.GetUnderlyingType(typeof(DiagnosticCode)));
        Assert.Equal(typeof(int), Enum.GetUnderlyingType(typeof(KatLangErrorCode)));

        var diagnosticCode = typeof(Diagnostic).GetProperty(nameof(Diagnostic.Code));
        Assert.NotNull(diagnosticCode);
        Assert.True(diagnosticCode!.GetMethod!.IsPublic);
        Assert.Equal(typeof(DiagnosticCode), diagnosticCode.PropertyType);

        var facadeCode = typeof(KatLangError).GetProperty(nameof(KatLangError.Code))!;
        var facadeSource = typeof(KatLangError).GetProperty(nameof(KatLangError.Source))!;
        var facadeIsLimit = typeof(KatLangError).GetProperty(nameof(KatLangError.IsResourceLimit))!;
        Assert.Equal(typeof(KatLangErrorCode), facadeCode.PropertyType);
        Assert.Equal(typeof(EvalError), facadeSource.PropertyType);
        Assert.Equal(typeof(bool), facadeIsLimit.PropertyType);
        Assert.True(facadeCode.GetMethod!.IsPublic);
        Assert.True(facadeSource.GetMethod!.IsPublic);
        Assert.True(facadeIsLimit.GetMethod!.IsPublic);
        Assert.Null(facadeCode.SetMethod);
        Assert.Null(facadeSource.SetMethod);
        Assert.Null(facadeIsLimit.SetMethod);
        Assert.Equal(
            NullabilityState.Nullable,
            new NullabilityInfoContext().Create(facadeSource).ReadState);
        Assert.Empty(typeof(KatLangError).GetConstructors(BindingFlags.Public | BindingFlags.Instance));

        var fromDiagnostic = typeof(KatLangError).GetMethod(
            nameof(KatLangError.FromDiagnostic),
            BindingFlags.Public | BindingFlags.Static,
            [typeof(Diagnostic)]);
        var fromEvalError = typeof(KatLangError).GetMethod(
            nameof(KatLangError.FromEvalError),
            BindingFlags.Public | BindingFlags.Static,
            [typeof(EvalError)]);
        Assert.NotNull(fromDiagnostic);
        Assert.NotNull(fromEvalError);
        Assert.Equal(typeof(KatLangError), fromDiagnostic!.ReturnType);
        Assert.Equal(typeof(KatLangError), fromEvalError!.ReturnType);

        var evalErrorIsLimit = typeof(EvalError).GetProperty(nameof(EvalError.IsResourceLimit));
        var evalErrorCode = typeof(EvalError).GetProperty(nameof(EvalError.Code));
        Assert.NotNull(evalErrorIsLimit);
        Assert.True(evalErrorIsLimit!.GetMethod!.IsPublic);
        Assert.Null(evalErrorIsLimit.SetMethod);
        Assert.NotNull(evalErrorCode);
        Assert.True(evalErrorCode!.GetMethod!.IsPublic);
        Assert.Null(evalErrorCode.SetMethod);

        // Existing compatibility surface: the three-parameter positional
        // constructor and three-component Deconstruct survive untouched.
        Assert.NotNull(typeof(Diagnostic).GetConstructor(
            [typeof(string), typeof(DiagnosticSeverity), typeof(SourceSpan)]));
        var deconstruct = typeof(Diagnostic).GetMethod(nameof(Diagnostic.Deconstruct))!;
        Assert.True(deconstruct.IsPublic);
        Assert.Equal(typeof(void), deconstruct.ReturnType);
        Assert.Equal(
            [typeof(string).MakeByRefType(), typeof(DiagnosticSeverity).MakeByRefType(), typeof(SourceSpan).MakeByRefType()],
            deconstruct.GetParameters().Select(static parameter => parameter.ParameterType));
        Assert.All(deconstruct.GetParameters(), static parameter => Assert.True(parameter.IsOut));

        // The code is init-only metadata, not a new positional parameter.
        Assert.NotNull(diagnosticCode.SetMethod);
        Assert.True(diagnosticCode.SetMethod!.IsPublic);
        Assert.Contains(
            typeof(System.Runtime.CompilerServices.IsExternalInit),
            diagnosticCode.SetMethod.ReturnParameter.GetRequiredCustomModifiers());
    }

    [Fact]
    public void RenderedMessages_AreUnchangedByStructuredIdentity()
    {
        // The classification channel is additive: rendering stays byte-for-byte.
        Assert.Equal("Unknown name: x", KatLangError.FromEvalError(new EvalError.UnknownName("x")).Message);
        Assert.Equal("Division by zero", KatLangError.FromEvalError(new EvalError.DivByZero()).Message);
        Assert.Equal(
            "Evaluation step limit of 8 was exceeded",
            KatLangError.FromEvalError(new EvalError.EvaluationStepLimitExceeded(8)).Message);
    }
}
