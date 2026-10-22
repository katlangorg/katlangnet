using KatLang.ParserFuzz;

namespace KatLang.Tests;

/// <summary>
/// SEM-2A: strict structured-error comparison for SAME-SOURCE relations, beside the unchanged
/// normalized cross-source policy.
///
/// <para>The cross-source policy (error kind plus resource payload) is deliberate: two
/// legitimately different spellings may name, position and contextualize an ordinary error
/// differently. Optimized-versus-generic execution, entry-point parity, the single-source budget
/// laws and independent runs promise more, and now compare every Q-67 field of the innermost
/// error — through the ONE classification Q-67 itself uses (<see cref="MetamorphicErrorDetail"/>).</para>
/// </summary>
public class MetamorphicStrictErrorPolicyTests
{
    private const string TwoParameters = "F(x, y) = x + y\nF(1)";
    private const string ThreeParameters = "F(x, y, z) = x + y + z\nF(1)";

    // ── E1 / E5: arity payloads through two real execution profiles ──────────

    [Fact]
    public void E1_E5_StrictSameSourceOptimizerParityRejectsADifferentArityPayload()
    {
        var testCase = FailingOptimizerCase(TwoParameters);
        Assert.Equal(MetamorphicErrorPolicy.StrictSameSource, testCase.ErrorPolicy);

        // Two real profiles of ONE source: optimizations on (left) and off (right).
        var execution = MetamorphicExecutor.Execute(testCase);
        Assert.True(execution.Accepted, execution.RejectionReason);
        var left = execution.Left!;
        var right = execution.Right!;
        Assert.Equal("on", left.OptimizerPolicy);
        Assert.Equal("off", right.OptimizerPolicy);
        Assert.Equal(Detail("arity", "arity", counts: [2, 1]), left.Semantic.ErrorDetail);
        Assert.Equal(left.Semantic.ErrorDetail, right.Semantic.ErrorDetail);
        Assert.True(MetamorphicComparator.StrictErrorComparisonApplies(testCase, left, right));
        Assert.Null(MetamorphicComparator.Compare(testCase, left, right));

        // Fault injection: the right member's observation replaced by a REAL ArityMismatch(3, 1).
        var other = Observe(ThreeParameters, enableOptimizations: false);
        Assert.Equal(left.Semantic.ErrorCategory, other.Semantic.ErrorCategory);
        Assert.Equal(left.Semantic.ErrorPayload, other.Semantic.ErrorPayload);
        var mismatch = Require(MetamorphicComparator.Compare(testCase, left, right with { Semantic = other.Semantic }));
        Assert.Equal(MetamorphicMismatchKind.SemanticErrorPayload, mismatch.Kind);
        Assert.Equal(MetamorphicMismatchClass.Semantic, mismatch.Class);
        Assert.Contains("strict same-source", mismatch.ComparedProperty, StringComparison.Ordinal);
        Assert.Contains("counts=[2, 1]", mismatch.LeftValue, StringComparison.Ordinal);
        Assert.Contains("counts=[3, 1]", mismatch.RightValue, StringComparison.Ordinal);

        // The SAME pair under the normalized policy is accepted: that relation never promised it.
        var normalized = testCase with { ErrorPolicy = MetamorphicErrorPolicy.Normalized };
        Assert.Null(MetamorphicComparator.Compare(normalized, left, right with { Semantic = other.Semantic }));
    }

    [Fact]
    public void E1_SyntheticArityPayloadsUnderEveryStrictRelation()
    {
        var left = Failed(new EvalError.ArityMismatch(2, 1));
        var right = Failed(new EvalError.ArityMismatch(3, 1));
        foreach (var relation in new[]
                 {
                     MetamorphicSemanticRelation.SemanticEqual,
                     MetamorphicSemanticRelation.SameStructuredOutcome,
                     MetamorphicSemanticRelation.IndependentRunStable,
                 })
        {
            var strict = StrictCase(relation);
            var mismatch = Require(MetamorphicComparator.Compare(strict, left, right));
            Assert.Equal(MetamorphicMismatchKind.SemanticErrorPayload, mismatch.Kind);
            Assert.Null(MetamorphicComparator.Compare(strict, left, Failed(new EvalError.ArityMismatch(2, 1))));
        }

        // Normalized SemanticEqual and SameStructuredOutcome accept it by design.
        Assert.Null(MetamorphicComparator.Compare(
            StrictCase(MetamorphicSemanticRelation.SemanticEqual) with { ErrorPolicy = MetamorphicErrorPolicy.Normalized }, left, right));
        Assert.Null(MetamorphicComparator.Compare(
            StrictCase(MetamorphicSemanticRelation.SameStructuredOutcome) with { ErrorPolicy = MetamorphicErrorPolicy.Normalized }, left, right));
    }

    // ── E2: variants are never collapsed ─────────────────────────────────────

    [Fact]
    public void E2_DifferentVariantsNeverCompareEqualEvenWhereQ67SharesACategory()
    {
        var pairs = new (EvalError Left, EvalError Right)[]
        {
            (new EvalError.ArityMismatch(2, 1), new EvalError.VariadicArityMismatch("F", 2, 1)),
            (new EvalError.ArityMismatch(2, 1), new EvalError.BadArity()),
            (new EvalError.BranchArityMismatch("F", 2, 1), new EvalError.BranchOutputArityMismatch("F", 2, 1)),
        };

        foreach (var (leftError, rightError) in pairs)
        {
            Assert.Equal(DifferentialErrors.Observe(leftError).Category, DifferentialErrors.Observe(rightError).Category);
            foreach (var policy in Enum.GetValues<MetamorphicErrorPolicy>())
            {
                var mismatch = Require(MetamorphicComparator.Compare(
                    StrictCase(MetamorphicSemanticRelation.SemanticEqual) with { ErrorPolicy = policy },
                    Failed(leftError), Failed(rightError)));
                Assert.Equal(MetamorphicMismatchKind.SemanticErrorCategory, mismatch.Kind);
            }
        }
    }

    // ── E3: the other comparable fields ──────────────────────────────────────

    [Fact]
    public void E3_EveryComparableFieldIsComparedUnderTheStrictPolicyOnly()
    {
        var pairs = new (EvalError Left, EvalError Right)[]
        {
            (new EvalError.VariadicArityMismatch("F", 2, 1), new EvalError.VariadicArityMismatch("F", 3, 1)),
            (new EvalError.VariadicArityMismatch("F", 2, 1), new EvalError.VariadicArityMismatch("F", 2, 0)),
            (new EvalError.BranchArityMismatch("F", 2, 1), new EvalError.BranchArityMismatch("F", 2, 3)),
            (new EvalError.BranchOutputArityMismatch("F", 1, 2), new EvalError.BranchOutputArityMismatch("F", 1, 3)),
            (new EvalError.UnknownName("a"), new EvalError.UnknownName("b")),
            (new EvalError.UnknownProperty("o", "A"), new EvalError.UnknownProperty("o", "B")),
            (new EvalError.UnresolvedImplicitParams(["x"]), new EvalError.UnresolvedImplicitParams(["x", "y"])),
            (new EvalError.UnresolvedImplicitParams(["x", "y"]), new EvalError.UnresolvedImplicitParams(["y", "x"])),
            (new EvalError.DuplicateProperty("A"), new EvalError.DuplicateProperty("a")),
        };

        foreach (var (leftError, rightError) in pairs)
        {
            var strict = Require(MetamorphicComparator.Compare(
                StrictCase(MetamorphicSemanticRelation.SemanticEqual), Failed(leftError), Failed(rightError)));
            Assert.Equal(MetamorphicMismatchKind.SemanticErrorPayload, strict.Kind);

            Assert.Null(MetamorphicComparator.Compare(
                StrictCase(MetamorphicSemanticRelation.SemanticEqual) with { ErrorPolicy = MetamorphicErrorPolicy.Normalized },
                Failed(leftError), Failed(rightError)));
        }

        // Partial payloads compare exactly the Q-67 subset: a variadic callee name is not in it.
        Assert.Null(MetamorphicComparator.Compare(
            StrictCase(MetamorphicSemanticRelation.SemanticEqual),
            Failed(new EvalError.VariadicArityMismatch("F", 2, 1)),
            Failed(new EvalError.VariadicArityMismatch("G", 2, 1))));
    }

    [Fact]
    public void E3_E7_ResourcePayloadsKeepTheirExistingComparisonUnderBothPolicies()
    {
        foreach (var policy in Enum.GetValues<MetamorphicErrorPolicy>())
        {
            var testCase = StrictCase(MetamorphicSemanticRelation.SemanticEqual) with { ErrorPolicy = policy };
            var limit = Require(MetamorphicComparator.Compare(
                testCase,
                Failed(new EvalError.CollectionSizeLimitExceeded(5, 9)),
                Failed(new EvalError.CollectionSizeLimitExceeded(6, 9))));
            Assert.Equal(MetamorphicMismatchKind.SemanticErrorPayload, limit.Kind);
            Assert.Equal(MetamorphicMismatchClass.ResourceBoundary, limit.Class);
            Assert.Equal("limit=5,requested=9", limit.LeftValue);

            var requested = Require(MetamorphicComparator.Compare(
                testCase,
                Failed(new EvalError.CollectionSizeLimitExceeded(5, 9)),
                Failed(new EvalError.CollectionSizeLimitExceeded(5, 10))));
            Assert.Equal(MetamorphicMismatchClass.ResourceBoundary, requested.Class);

            var verdict = Require(MetamorphicComparator.Compare(
                testCase, Failed(new EvalError.EvaluationStepLimitExceeded(10)), Failed(new EvalError.ArityMismatch(2, 1))));
            Assert.Equal(MetamorphicMismatchKind.ResourceLimitVerdict, verdict.Kind);

            // Equal resource failures pass; their partial counters are never compared.
            var stopped = Failed(new EvalError.EvaluationStepLimitExceeded(10));
            Assert.Null(MetamorphicComparator.Compare(testCase, stopped, stopped with { MaterializedItems = 99 }));
            Assert.False(MetamorphicComparator.WorkIsComparable(stopped, stopped));
        }
    }

    [Fact]
    public void E7_TheBoundaryLawStillReadsTheDeclaredStopKind()
    {
        var boundary = StrictCase(MetamorphicSemanticRelation.SameResourceBoundary) with
        {
            BoundaryStop = MetamorphicBoundaryStop.ResourceError,
            ExpectedResourceKind = nameof(EvalError.EvaluationStepLimitExceeded),
        };
        var ok = new MetamorphicOperationalObservation(
            MetamorphicSemanticObservation.OfValue(new Result.Atom(1m), 1), 1, 0, 0, 1, "on");

        Assert.Null(MetamorphicComparator.Compare(boundary, ok, Failed(new EvalError.EvaluationStepLimitExceeded(3))));
        Assert.Equal(
            MetamorphicMismatchKind.BoundaryStopKind,
            Require(MetamorphicComparator.Compare(boundary, ok, Failed(new EvalError.CollectionSizeLimitExceeded(1, 2)))).Kind);
        Assert.Equal(
            MetamorphicMismatchKind.BoundaryStopKind,
            Require(MetamorphicComparator.Compare(boundary, ok, Failed(new EvalError.ArityMismatch(2, 1)))).Kind);
    }

    // ── E4: cross-source relations keep the normalized policy ────────────────

    [Fact]
    public void E4_RegisteredPoliciesAreStrictExactlyForSameSourceRelations()
    {
        foreach (var definition in MetamorphicFamilyRegistry.All)
        {
            if (definition.Family is MetamorphicFamily.OptimizerGenericParity
                or MetamorphicFamily.EntryPointParity
                or MetamorphicFamily.BudgetLaw)
            {
                continue;
            }

            foreach (var parameters in MetamorphicTemplates.EnumerateStratifiedParameters()
                         .Where(parameters => parameters.Family == definition.Family).Take(3))
            {
                var testCase = MetamorphicTemplates.Build(parameters);
                Assert.Equal(MetamorphicErrorPolicy.Normalized, testCase.ErrorPolicy);
            }
        }

        Assert.Equal(MetamorphicErrorPolicy.StrictSameSource, BuildOf(MetamorphicFamily.OptimizerGenericParity, 0, 0, 0).ErrorPolicy);
        Assert.Equal(MetamorphicErrorPolicy.StrictSameSource, BuildOf(MetamorphicFamily.EntryPointParity, 0, 0, 0).ErrorPolicy);
        for (var law = 0; law < MetamorphicBudgetLawTemplate.Laws.Length; law++)
        {
            var testCase = BuildOf(MetamorphicFamily.BudgetLaw, 0, law, 0, 0);
            var sameSource = string.Equals(testCase.LeftSource, testCase.RightSource, StringComparison.Ordinal);
            Assert.Equal(
                MetamorphicBudgetLawTemplate.Laws[law] == MetamorphicBudgetLaw.EquivalentFormBoundaryParity
                    ? MetamorphicErrorPolicy.Normalized
                    : MetamorphicErrorPolicy.StrictSameSource,
                testCase.ErrorPolicy);
            Assert.True(sameSource || testCase.ErrorPolicy == MetamorphicErrorPolicy.Normalized);
        }
    }

    [Fact]
    public void E4_NormalizedCrossSourceRelationsStillAcceptRenamedAndRecontextualizedErrors()
    {
        var normalized = StrictCase(MetamorphicSemanticRelation.SemanticEqual) with { ErrorPolicy = MetamorphicErrorPolicy.Normalized };
        Assert.Null(MetamorphicComparator.Compare(
            normalized, Failed(new EvalError.UnknownName("x")), Failed(new EvalError.UnknownName("renamed"))));
        Assert.Null(MetamorphicComparator.Compare(
            normalized,
            Failed(new EvalError.WithContext("in F", new EvalError.ArityMismatch(2, 1))),
            Failed(new EvalError.ArityMismatch(3, 1))));

        // Two real, differently named programs under a cross-source case: accepted as before.
        var testCase = MetamorphicTemplates.Build(MetamorphicDecoder.Decode([0, 0, 0, 1, 1, 1])) with
        {
            LeftSource = TwoParameters,
            RightSource = "Rename(a, b) = a + b\nRename(7)",
        };
        var execution = MetamorphicExecutor.Execute(testCase);
        Assert.True(execution.Accepted, execution.RejectionReason);
        Assert.False(MetamorphicComparator.StrictErrorComparisonApplies(testCase, execution.Left!, execution.Right!));
        Assert.Null(MetamorphicComparator.Compare(testCase, execution.Left!, execution.Right!));

        // Declaring strictness over two sources is a harness defect, never a silent comparison.
        Assert.Throws<MetamorphicHarnessException>(() => MetamorphicComparator.Compare(
            testCase with { ErrorPolicy = MetamorphicErrorPolicy.StrictSameSource }, execution.Left!, execution.Right!));
    }

    // ── E6: unavailable structured facets ────────────────────────────────────

    [Fact]
    public void E6_ASurfaceWithoutStructuredErrorsIsNeverCreditedWithAStrictComparison()
    {
        var entry = BuildOf(MetamorphicFamily.EntryPointParity, 0, 0, 0) with
        {
            LeftSource = TwoParameters,
            RightSource = TwoParameters,
            LeftProfile = new MetamorphicExecutionProfile(MetamorphicSurface.EvaluatorRun, null, true),
            RightProfile = new MetamorphicExecutionProfile(MetamorphicSurface.EngineRun, null, true),
        };
        var execution = MetamorphicExecutor.Execute(entry);
        Assert.True(execution.Accepted, execution.RejectionReason);
        var left = execution.Left!;
        var right = execution.Right!;

        Assert.NotNull(left.Semantic.ErrorDetail);
        Assert.Null(right.Semantic.ErrorDetail);
        Assert.Null(right.Semantic.ErrorCategory);
        Assert.False(MetamorphicComparator.StrictErrorComparisonApplies(entry, left, right));
        Assert.Null(MetamorphicComparator.Compare(entry, left, right));

        // Every surface: the detail exists exactly where the structured-error facet is claimed.
        foreach (var surface in MetamorphicSurfaces.All)
        {
            var observation = ObserveThrough(surface.Surface, TwoParameters);
            Assert.Equal("err", observation.Semantic.Outcome);
            if (surface.Facets.HasFlag(MetamorphicFacets.StructuredError))
                Assert.Equal(Detail("arity", "arity", counts: [2, 1]), observation.Semantic.ErrorDetail);
            else
                Assert.Null(observation.Semantic.ErrorDetail);
        }

        // An adapter that CLAIMS the facet but projects no detail cannot pass by comparing absences.
        var forged = left with { Semantic = MetamorphicSemanticObservation.Failure("ArityMismatch", null, false) };
        var strict = StrictCase(MetamorphicSemanticRelation.SemanticEqual);
        Assert.Throws<MetamorphicHarnessException>(() => MetamorphicComparator.Compare(strict, left, forged));
    }

    // ── E8: contexts and messages ────────────────────────────────────────────

    [Fact]
    public void E8_ContextsAndMessagesNeverBecomeStringComparisons()
    {
        var strict = StrictCase(MetamorphicSemanticRelation.SemanticEqual);

        // Innermost structured error only: wrapper prose and depth are not compared.
        Assert.Null(MetamorphicComparator.Compare(
            strict,
            Failed(new EvalError.WithContext("while calling F", new EvalError.ArityMismatch(2, 1))),
            Failed(new EvalError.WithContext("outer", new EvalError.WithContext("inner", new EvalError.ArityMismatch(2, 1))))));

        // ...while the innermost payload still is.
        Assert.Equal(
            MetamorphicMismatchKind.SemanticErrorPayload,
            Require(MetamorphicComparator.Compare(
                strict,
                Failed(new EvalError.WithContext("same", new EvalError.ArityMismatch(2, 1))),
                Failed(new EvalError.WithContext("same", new EvalError.ArityMismatch(3, 1))))).Kind);

        // Category-only variants carry descriptions, not structured data: never compared as text.
        Assert.Null(MetamorphicComparator.Compare(
            strict, Failed(new EvalError.TypeMismatch("expected a number")), Failed(new EvalError.TypeMismatch("other words"))));

        // Exact fields still compare in full, but a pathological name must not become an
        // unbounded diagnostic. Escape lone surrogates and controls before writing a report.
        var longName = "\n\0\uD800" + new string('x', 10_000);
        var large = Require(MetamorphicComparator.Compare(
            strict, Failed(new EvalError.UnknownName(longName)), Failed(new EvalError.UnknownName(longName + "y"))));
        Assert.Equal(MetamorphicMismatchKind.SemanticErrorPayload, large.Kind);
        foreach (var diagnostic in new[] { large.LeftValue, large.RightValue })
        {
            Assert.True(diagnostic.Length < 300, $"diagnostic length {diagnostic.Length}");
            Assert.DoesNotContain(diagnostic, unit => char.IsControl(unit) || char.IsSurrogate(unit));
        }
    }

    // ── Q-67 consistency: one classification, two consumers ──────────────────

    [Fact]
    public void Q67_DifferentialErrorsIsExactlyTheSharedDetail()
    {
        foreach (var contract in DifferentialErrorContracts.All)
        {
            var detail = MetamorphicErrorDetail.Observe(contract.Error);
            var q67 = DifferentialErrors.Observe(contract.Error);
            Assert.Equal(q67.Category, detail.Category);
            Assert.Equal(q67.Comparison.ToString(), detail.Comparison.ToString());
            Assert.Equal(q67.Payload, detail.Kind is null ? null : new SharedErrorPayload(detail.Kind, detail.Names, detail.Counts));

            // The metamorphic observation carries the same detail, context-insensitively.
            Assert.Equal(detail, MetamorphicSemanticObservation.OfError(new EvalError.WithContext("ctx", contract.Error)).ErrorDetail);
        }
    }

    // ── Helpers ──────────────────────────────────────────────────────────────

    private static MetamorphicErrorDetail Detail(string category, string kind, string[]? names = null, int[]? counts = null)
        => new(category, MetamorphicErrorComparison.Comparable, kind, [.. names ?? []], [.. counts ?? []]);

    private static MetamorphicOperationalObservation Failed(EvalError error)
        => new(MetamorphicSemanticObservation.OfError(error), 3, 2, 0, 1, "on");

    /// <summary>A same-source case declaring the strict policy, whatever relation the test needs.</summary>
    private static MetamorphicCase StrictCase(MetamorphicSemanticRelation relation)
        => FailingOptimizerCase(TwoParameters) with
        {
            SemanticRelation = relation,
            OperationalRelation = MetamorphicOperationalRelation.NotCompared,
        };

    /// <summary>
    /// The optimizer-parity family over a failing source. Its optimizer-path evidence gate is
    /// dropped (a failing program proves no path); everything else is the family's own case.
    /// </summary>
    private static MetamorphicCase FailingOptimizerCase(string source)
        => BuildOf(MetamorphicFamily.OptimizerGenericParity, 0, 0, 0) with
        {
            LeftSource = source,
            RightSource = source,
            LeftEvidence = MetamorphicSideEvidence.None,
            RightEvidence = MetamorphicSideEvidence.None,
        };

    private static MetamorphicCase BuildOf(MetamorphicFamily family, params int[] extras)
    {
        var payload = new byte[MetamorphicParameters.CommonPayloadLength + extras.Length];
        payload[0] = (byte)MetamorphicDecoder.FamilyTable.IndexOf(family);
        payload[3] = 1;
        payload[4] = 1;
        payload[5] = 1;
        for (var i = 0; i < extras.Length; i++) payload[MetamorphicParameters.CommonPayloadLength + i] = (byte)extras[i];
        return MetamorphicTemplates.Build(MetamorphicDecoder.Decode(payload));
    }

    private static MetamorphicOperationalObservation Observe(string source, bool enableOptimizations)
    {
        Assert.True(MetamorphicExecutor.TryObserve(source, null, enableOptimizations, out var observation, out var reason), reason);
        return observation;
    }

    private static MetamorphicOperationalObservation ObserveThrough(MetamorphicSurface surface, string source)
    {
        var profile = new MetamorphicExecutionProfile(surface, null, EnableOptimizations: true);
        Assert.True(
            MetamorphicSurfaces.TryObserve(
                source, profile, MetamorphicExecutor.OptionsFor(profile), collectEvidence: false,
                out var observation, out var reason),
            reason);
        return observation;
    }

    private static MetamorphicMismatch Require(MetamorphicMismatch? mismatch)
        => Assert.IsType<MetamorphicMismatch>(mismatch);
}
