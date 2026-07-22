using System.Collections.Immutable;
using System.Globalization;
using System.Reflection;
using System.Text.RegularExpressions;
using KatLang.ParserFuzz;

namespace KatLang.Tests;

/// <summary>
/// Phase 4's INDEPENDENT audit of the metamorphic harness: the checks that ask whether the
/// measuring apparatus can be trusted, rather than whether the language is right.
///
/// <para>The Phase 1-3 suites each verify their own families. These verify properties that hold
/// ACROSS families and would otherwise be nobody's job — a surface that declares a facet it
/// cannot fill, a comparator branch no test ever reaches, a directional relation that would pass
/// just as happily reversed, a rejection nothing names, a fingerprint two materially different
/// cases share, static state anywhere in the harness. Each one is a way the campaign could report
/// a false relation or a false mismatch without any individual family being wrong.</para>
///
/// <para>Nothing here executes a long campaign or asserts a wall-clock time; the bounds checks
/// are structural.</para>
/// </summary>
public class MetamorphicPhase4AuditTests
{
    private static List<MetamorphicParameters> Stratified { get; } =
        MetamorphicTemplates.EnumerateStratifiedParameters().ToList();

    private static IEnumerable<MetamorphicParameters> OfFamily(MetamorphicFamily family)
        => Stratified.Where(parameters => parameters.Family == family);

    /// <summary>One representative parameter point per registered family.</summary>
    private static IEnumerable<MetamorphicParameters> OnePerFamily()
        => MetamorphicFamilyRegistry.All.Select(definition => OfFamily(definition.Family).First());

    // ── Family soundness: a declared facet must be a facet the adapter can fill ──

    /// <summary>Programs covering every value kind and every failure channel a surface can meet.</summary>
    private static readonly (string Id, string Source, bool Parses)[] SurfaceProbes =
    [
        ("scalar", "Output = 1 + 2", true),
        ("collection", "Output = range(1, 4)", true),
        ("list", "Output = [1, [2, 3]]", true),
        ("empty-sequence", "Output = ()", true),
        ("string", "Output = 'abc'", true),
        ("top-level-property", "DisplayDecimals = 2\nOutput = 1.5", true),
        ("semantic-failure", "Output = min([])", true),
        ("resource-failure", "Output = range(1, 200000).count", true),
        ("no-program-output", "MmA = 1", true),
        ("parse-failure", "Output = 1 ; 2", false),
    ];

    /// <summary>
    /// A surface may claim a facet only when its adapter really produces it, and may never fill
    /// one it did not claim.
    ///
    /// <para>This is what stops <c>CompareSharedFacets</c> from comparing two absences. The
    /// comparator reads <c>left.Projection?.HostAtoms</c> when both sides claim
    /// <c>HostAtoms</c>; if a claiming surface could return a null projection, two nulls would
    /// compare equal and the pair would pass having verified nothing. Today that is impossible by
    /// construction — this test is what keeps it impossible when a surface is added.</para>
    /// </summary>
    [Fact]
    public void EverySurface_FillsExactlyTheFacetsItDeclares()
    {
        var observed = 0;

        foreach (var definition in MetamorphicSurfaces.All)
        foreach (var (id, source, parses) in SurfaceProbes)
        {
            var profile = new MetamorphicExecutionProfile(definition.Surface, Limits: null, EnableOptimizations: true);
            var ran = MetamorphicSurfaces.TryObserve(
                source, profile, MetamorphicExecutor.OptionsFor(profile),
                collectEvidence: false, out var observation, out var reason);

            if (!ran)
            {
                Assert.True(
                    definition.RequiresParsableSource && !parses,
                    $"{definition.Id}/{id}: refused a program it declares it can run ({reason}).");
                continue;
            }

            observed++;
            var where = $"{definition.Id}/{id}";
            var facets = observation.Facets;
            Assert.Equal(definition.Facets, facets);
            Assert.Equal(definition.Id, observation.Surface);

            var succeeded = observation.Semantic.Outcome == "ok";

            // A claimed facet must carry real data. Value-bearing facets are only required to be
            // filled on SUCCESS: "this failed run produced no atoms" is a fact both sides state,
            // not an absence, and the outcome comparison has already run by then.
            if (facets.HasFlag(MetamorphicFacets.HostAtoms) && succeeded)
            {
                Assert.NotNull(observation.Projection);
                Assert.NotNull(observation.Projection!.HostAtoms);
            }

            if (facets.HasFlag(MetamorphicFacets.RenderedText))
            {
                Assert.NotNull(observation.Projection);
                Assert.NotNull(observation.Projection!.RenderedText);
                Assert.NotEqual(MetamorphicSurfaceProjection.NoRendering, observation.Projection.RenderedProjection);
                Assert.True(observation.Projection.RenderedLimit >= 0, $"{where}: rendering surface has no limit.");
            }

            if (facets.HasFlag(MetamorphicFacets.TopLevelProperty))
            {
                Assert.NotNull(observation.Projection);
                Assert.NotNull(observation.Projection!.TopLevelProperty);
            }

            if (facets.HasFlag(MetamorphicFacets.Structure) && succeeded)
                Assert.NotNull(observation.Semantic.Structure);

            if (facets.HasFlag(MetamorphicFacets.EmittedCount) && succeeded)
                Assert.NotNull(observation.Semantic.EmittedCount);

            // An UNCLAIMED facet must stay empty, or the intersection rule would be comparing a
            // field one side is not entitled to report.
            if (!facets.HasFlag(MetamorphicFacets.Structure))
                Assert.Null(observation.Semantic.Structure);
            if (!facets.HasFlag(MetamorphicFacets.EmittedCount))
                Assert.Null(observation.Semantic.EmittedCount);
            if (!facets.HasFlag(MetamorphicFacets.StructuredError))
            {
                Assert.Null(observation.Semantic.ErrorCategory);
                Assert.Null(observation.Semantic.ErrorPayload);
                Assert.False(observation.Semantic.IsResourceLimit);
            }

            if (!facets.HasFlag(MetamorphicFacets.HostAtoms))
                Assert.Null(observation.Projection?.HostAtoms);
            if (!facets.HasFlag(MetamorphicFacets.RenderedText))
                Assert.Null(observation.Projection?.RenderedText);
            if (!facets.HasFlag(MetamorphicFacets.TopLevelProperty))
                Assert.Null(observation.Projection?.TopLevelProperty);

            // Only the observed evaluator entry point hands back a budget; every other surface
            // must report structural zeroes AND must not claim the counters facet.
            Assert.Equal(
                definition.Surface == MetamorphicSurface.EvaluatorRunCountedObserved,
                facets.HasFlag(MetamorphicFacets.OperationalCounters));

            if (!facets.HasFlag(MetamorphicFacets.OperationalCounters))
            {
                Assert.Equal(0, observation.EvaluationSteps);
                Assert.Equal(0, observation.MaterializedItems);
                Assert.Equal(0, observation.MaterializedStringChars);
                Assert.Equal(0, observation.PeakDynamicDepth);
            }
        }

        Assert.True(observed > 60, $"Only {observed} surface observations ran; the sweep did not cover the surfaces.");
    }

    /// <summary>
    /// Entry-point parity must never pass on two absences: whenever both surfaces SUCCEEDED, every
    /// facet the pair is compared on carries real data on both sides.
    /// </summary>
    [Fact]
    public void EntryPointPairs_CompareRealDataRatherThanTwoAbsences()
    {
        var compared = 0;

        foreach (var parameters in OfFamily(MetamorphicFamily.EntryPointParity))
        {
            var execution = MetamorphicExecutor.Execute(MetamorphicTemplates.Build(parameters));
            if (execution is not { Accepted: true, Left: { } left, Right: { } right }) continue;
            if (left.Semantic.Outcome != "ok" || right.Semantic.Outcome != "ok") continue;

            compared++;
            var shared = left.Facets & right.Facets;
            var where = parameters.ToString();

            Assert.NotEqual(MetamorphicFacets.Outcome, shared);

            if (shared.HasFlag(MetamorphicFacets.Structure))
            {
                Assert.NotNull(left.Semantic.Structure);
                Assert.NotNull(right.Semantic.Structure);
            }

            if (shared.HasFlag(MetamorphicFacets.EmittedCount))
            {
                Assert.NotNull(left.Semantic.EmittedCount);
                Assert.NotNull(right.Semantic.EmittedCount);
            }

            if (shared.HasFlag(MetamorphicFacets.HostAtoms))
            {
                Assert.True(left.Projection?.HostAtoms is not null, $"{where}: left claims atoms but has none.");
                Assert.True(right.Projection?.HostAtoms is not null, $"{where}: right claims atoms but has none.");
            }

            if (shared.HasFlag(MetamorphicFacets.RenderedText))
            {
                Assert.True(left.Projection?.RenderedText is not null, $"{where}: left claims rendering but has none.");
                Assert.True(right.Projection?.RenderedText is not null, $"{where}: right claims rendering but has none.");
            }

            if (shared.HasFlag(MetamorphicFacets.TopLevelProperty))
            {
                Assert.NotNull(left.Projection?.TopLevelProperty);
                Assert.NotNull(right.Projection?.TopLevelProperty);
            }
        }

        Assert.True(compared > 40, $"Only {compared} successful entry-point pairs were checked.");
    }

    // ── Relation audit ───────────────────────────────────────────────────────

    private static MetamorphicOperationalObservation Reference(
        string structure = "3", int emitted = 1, long steps = 20, long items = 8, long chars = 0, int depth = 4)
        => new(MetamorphicSemanticObservation.Success(structure, emitted), steps, items, chars, depth, "on");

    private static MetamorphicCase CaseWith(
        MetamorphicSemanticRelation semantic, MetamorphicOperationalRelation operational)
        => MetamorphicTemplates.Build(Stratified[0]) with
        {
            SemanticRelation = semantic,
            OperationalRelation = operational,
        };

    /// <summary>
    /// Equality relations must give the same verdict whichever way round the two observations are
    /// handed to them; directional relations must NOT.
    ///
    /// <para>A directional relation that happened to be symmetric would be an equality wearing an
    /// inequality's name, and the orientation bug it is supposed to catch — an optimized run that
    /// costs more than the generic one, a dotted form that materializes more than its ordinary
    /// spelling — would pass. So each directional relation is required to have a witness pair that
    /// passes one way and fails the other.</para>
    /// </summary>
    [Fact]
    public void EqualityRelations_AreSymmetricAndDirectionalRelationsAreNot()
    {
        var cheap = Reference(steps: 10, items: 4);
        var costly = Reference(steps: 30, items: 12);

        foreach (var relation in Enum.GetValues<MetamorphicOperationalRelation>())
        {
            var testCase = CaseWith(MetamorphicSemanticRelation.SemanticEqual, relation);
            var forward = MetamorphicComparator.Compare(testCase, cheap, costly);
            var reverse = MetamorphicComparator.Compare(testCase, costly, cheap);

            switch (relation)
            {
                case MetamorphicOperationalRelation.NotCompared:
                    Assert.Null(forward);
                    Assert.Null(reverse);
                    break;

                case MetamorphicOperationalRelation.ExactMaterializationEqual:
                case MetamorphicOperationalRelation.ExactObservedWorkEqual:
                case MetamorphicOperationalRelation.IdenticalWork:
                    // Symmetric: both directions must agree that this pair is not equal.
                    Assert.NotNull(forward);
                    Assert.NotNull(reverse);
                    Assert.Equal(forward!.Kind, reverse!.Kind);
                    break;

                case MetamorphicOperationalRelation.MaterializationNeverIncreases:
                    // "right never exceeds left": cheap-left/costly-right must fail.
                    Assert.NotNull(forward);
                    Assert.Null(reverse);
                    break;

                case MetamorphicOperationalRelation.WorkNeverIncreases:
                    // "left never exceeds right": cheap-left/costly-right must pass.
                    Assert.Null(forward);
                    Assert.NotNull(reverse);
                    break;

                default:
                    Assert.Fail($"Operational relation {relation} has no declared symmetry expectation.");
                    break;
            }
        }

        // The two directional relations point in OPPOSITE directions by design; a refactor that
        // accidentally unified them would still satisfy each case above on its own.
        var neverIncreases = CaseWith(
            MetamorphicSemanticRelation.SemanticEqual, MetamorphicOperationalRelation.MaterializationNeverIncreases);
        var workNeverIncreases = CaseWith(
            MetamorphicSemanticRelation.SemanticEqual, MetamorphicOperationalRelation.WorkNeverIncreases);
        Assert.NotNull(MetamorphicComparator.Compare(neverIncreases, cheap, costly));
        Assert.Null(MetamorphicComparator.Compare(workNeverIncreases, cheap, costly));
    }

    /// <summary>
    /// The two DIRECTIONAL semantic relations are likewise orientation-sensitive: monotonic
    /// success places its obligation only on the right member, and the boundary law requires the
    /// left member to succeed and the right one to stop.
    /// </summary>
    [Fact]
    public void DirectionalSemanticRelations_AreOrientationSensitive()
    {
        var ok = Reference();
        var stopped = new MetamorphicOperationalObservation(
            MetamorphicSemanticObservation.Failure(nameof(EvalError.EvaluationStepLimitExceeded), "1", true),
            0, 0, 0, 0, "on");

        var monotone = CaseWith(MetamorphicSemanticRelation.MonotonicSuccess, MetamorphicOperationalRelation.NotCompared);

        // ok -> stopped is a regression; stopped -> ok places no obligation at all.
        var regression = MetamorphicComparator.Compare(monotone, ok, stopped);
        Assert.NotNull(regression);
        Assert.Equal(MetamorphicMismatchKind.MonotonicRegression, regression!.Kind);
        Assert.Null(MetamorphicComparator.Compare(monotone, stopped, ok));

        var boundary = CaseWith(
            MetamorphicSemanticRelation.SameResourceBoundary, MetamorphicOperationalRelation.NotCompared) with
        {
            BoundaryStop = MetamorphicBoundaryStop.ResourceError,
            ExpectedResourceKind = nameof(EvalError.EvaluationStepLimitExceeded),
        };

        Assert.Null(MetamorphicComparator.Compare(boundary, ok, stopped));

        var reversed = MetamorphicComparator.Compare(boundary, stopped, ok);
        Assert.NotNull(reversed);
        Assert.Equal(MetamorphicMismatchKind.BoundarySuccess, reversed!.Kind);
    }

    /// <summary>
    /// Every comparator branch is reachable and produces its own mismatch kind.
    ///
    /// <para>A kind no constructed pair can produce is either dead code or — worse — a comparison
    /// that silently never fires. This enumerates the whole enum rather than sampling it, so a new
    /// kind cannot be added without a pair that provokes it.</para>
    /// </summary>
    [Fact]
    public void EveryMismatchKind_IsProducedByADeliberatelyBrokenPair()
    {
        var produced = new Dictionary<MetamorphicMismatchKind, MetamorphicMismatchClass>();

        void Record(MetamorphicCase testCase, MetamorphicOperationalObservation left, MetamorphicOperationalObservation right)
        {
            var mismatch = MetamorphicComparator.Compare(testCase, left, right);
            Assert.NotNull(mismatch);
            produced[mismatch!.Kind] = mismatch.Class;
        }

        var equal = CaseWith(
            MetamorphicSemanticRelation.SemanticEqual, MetamorphicOperationalRelation.ExactObservedWorkEqual);
        var reference = Reference();

        // Semantic class.
        Record(equal, reference, new MetamorphicOperationalObservation(
            MetamorphicSemanticObservation.Failure("ArityMismatch", null, false), 20, 8, 0, 4, "on"));
        Record(equal, reference, reference with { Semantic = MetamorphicSemanticObservation.Success("4", 1) });
        Record(equal, reference, reference with { Semantic = MetamorphicSemanticObservation.Success("3", 2) });

        var failed = new MetamorphicOperationalObservation(
            MetamorphicSemanticObservation.Failure("ArityMismatch", "1", false), 20, 8, 0, 4, "on");
        Record(equal, failed, failed with { Semantic = MetamorphicSemanticObservation.Failure("NotCallable", "1", false) });
        Record(equal, failed, failed with { Semantic = MetamorphicSemanticObservation.Failure("ArityMismatch", "2", false) });
        Record(equal, failed, failed with
        {
            Semantic = MetamorphicSemanticObservation.Failure(
                nameof(EvalError.EvaluationStepLimitExceeded), "1", true),
        });

        // Operational class.
        Record(equal, reference, reference with { MaterializedItems = 9 });
        Record(equal, reference, reference with { MaterializedStringChars = 3 });
        Record(equal, reference, reference with { EvaluationSteps = 21 });
        Record(equal, reference, reference with { PeakDynamicDepth = 5 });

        // Projection classes: host atoms, the property channel, and rendering.
        var shared = CaseWith(
            MetamorphicSemanticRelation.SameStructuredOutcome, MetamorphicOperationalRelation.NotCompared);
        var atoms = Projected(MetamorphicFacets.Outcome | MetamorphicFacets.HostAtoms, hostAtoms: "1 2");
        Record(shared, atoms, Projected(MetamorphicFacets.Outcome | MetamorphicFacets.HostAtoms, hostAtoms: "1 3"));

        var property = Projected(MetamorphicFacets.Outcome | MetamorphicFacets.TopLevelProperty, topLevelProperty: "2#1");
        Record(shared, property, Projected(
            MetamorphicFacets.Outcome | MetamorphicFacets.TopLevelProperty, topLevelProperty: "3#1"));

        var rendered = Projected(
            MetamorphicFacets.Outcome | MetamorphicFacets.RenderedText,
            renderedText: "3", renderedProjection: MetamorphicSurfaceProjection.StructuredDisplay, renderedLimit: 16);
        Record(shared, rendered, rendered with
        {
            Projection = rendered.Projection! with { RenderedText = "4" },
        });

        // The per-side rendering bound: more units returned than the surface's limit allows.
        Record(shared, rendered with
        {
            Projection = rendered.Projection! with { RenderedText = new string('x', 17) },
        }, rendered);

        // Boundary, monotonicity, and isolation.
        var stopped = new MetamorphicOperationalObservation(
            MetamorphicSemanticObservation.Failure(nameof(EvalError.EvaluationStepLimitExceeded), "1", true),
            0, 0, 0, 0, "on");
        var monotone = CaseWith(MetamorphicSemanticRelation.MonotonicSuccess, MetamorphicOperationalRelation.NotCompared);
        Record(monotone, reference, stopped);

        var boundary = CaseWith(
            MetamorphicSemanticRelation.SameResourceBoundary, MetamorphicOperationalRelation.NotCompared) with
        {
            BoundaryStop = MetamorphicBoundaryStop.ResourceError,
            ExpectedResourceKind = nameof(EvalError.EvaluationStepLimitExceeded),
        };
        Record(boundary, stopped, stopped);
        Record(boundary, reference, reference);

        var isolation = CaseWith(
            MetamorphicSemanticRelation.IndependentRunStable, MetamorphicOperationalRelation.IdenticalWork);
        Record(isolation, reference, reference with { OptimizerPolicy = "off" });

        var missing = Enum.GetValues<MetamorphicMismatchKind>().Where(kind => !produced.ContainsKey(kind)).ToList();
        Assert.True(
            missing.Count == 0,
            "No constructed pair reaches these comparator branches: " + string.Join(", ", missing));

        // The boundary and isolation kinds must keep their own CLASSES, so a campaign summary can
        // tell a resource-policy finding from a state leak without reading the text.
        Assert.Equal(MetamorphicMismatchClass.ResourceBoundary, produced[MetamorphicMismatchKind.MonotonicRegression]);
        Assert.Equal(MetamorphicMismatchClass.ResourceBoundary, produced[MetamorphicMismatchKind.BoundarySuccess]);
        Assert.Equal(MetamorphicMismatchClass.ResourceBoundary, produced[MetamorphicMismatchKind.BoundaryStopKind]);
        Assert.Equal(MetamorphicMismatchClass.StateIsolation, produced[MetamorphicMismatchKind.IndependentRunState]);
        Assert.Equal(MetamorphicMismatchClass.Rendering, produced[MetamorphicMismatchKind.RenderedLength]);
        Assert.Equal(MetamorphicMismatchClass.Rendering, produced[MetamorphicMismatchKind.RenderedText]);
    }

    private static MetamorphicOperationalObservation Projected(
        MetamorphicFacets facets,
        string? hostAtoms = null,
        string? renderedText = null,
        string renderedProjection = MetamorphicSurfaceProjection.NoRendering,
        int renderedLimit = -1,
        string? topLevelProperty = null)
        => new(MetamorphicSemanticObservation.OutcomeOnly(failed: false), 0, 0, 0, 0, "on")
        {
            Facets = facets,
            Projection = new MetamorphicSurfaceProjection(
                hostAtoms, renderedText, renderedProjection, renderedLimit, topLevelProperty),
        };

    /// <summary>
    /// Every declared relation value is implemented by the comparator AND declared by at least one
    /// registered family. A relation nothing declares is dead weight; a relation the comparator
    /// does not implement throws at campaign time rather than at build time.
    /// </summary>
    [Fact]
    public void EveryDeclaredRelation_IsImplementedAndReachedByARegisteredFamily()
    {
        var reference = Reference();

        foreach (var semantic in Enum.GetValues<MetamorphicSemanticRelation>())
        {
            var testCase = CaseWith(semantic, MetamorphicOperationalRelation.NotCompared) with
            {
                BoundaryStop = semantic == MetamorphicSemanticRelation.SameResourceBoundary
                    ? MetamorphicBoundaryStop.ResourceError
                    : MetamorphicBoundaryStop.None,
                ExpectedResourceKind = nameof(EvalError.EvaluationStepLimitExceeded),
            };

            // Implemented: comparing a pair against it must not throw "no comparison implemented".
            _ = MetamorphicComparator.Compare(testCase, reference, reference);
        }

        foreach (var operational in Enum.GetValues<MetamorphicOperationalRelation>())
            _ = MetamorphicComparator.Compare(CaseWith(MetamorphicSemanticRelation.SemanticEqual, operational), reference, reference);

        var declaredSemantic = new HashSet<MetamorphicSemanticRelation>();
        var declaredOperational = new HashSet<MetamorphicOperationalRelation>();
        foreach (var parameters in Stratified)
        {
            var testCase = MetamorphicTemplates.Build(parameters);
            declaredSemantic.Add(testCase.SemanticRelation);
            declaredOperational.Add(testCase.OperationalRelation);
        }

        var unusedSemantic = Enum.GetValues<MetamorphicSemanticRelation>().Except(declaredSemantic).ToList();
        var unusedOperational = Enum.GetValues<MetamorphicOperationalRelation>().Except(declaredOperational).ToList();
        Assert.True(unusedSemantic.Count == 0, "No family declares: " + string.Join(", ", unusedSemantic));
        Assert.True(unusedOperational.Count == 0, "No family declares: " + string.Join(", ", unusedOperational));
    }

    // ── Preconditions and rejection audit ────────────────────────────────────

    /// <summary>
    /// Every rejection is NAMED, in one stable vocabulary, and no family is rejected outright.
    ///
    /// <para>Rejection is how the harness declines to compare a pair it cannot justify, so an
    /// unnamed or ad-hoc reason is invisible in a campaign summary. The name shape is enforced,
    /// the per-family rate is required to leave real coverage behind, and every reason must be one
    /// this repository knows about.</para>
    /// </summary>
    [Fact]
    public void EveryRejection_IsNamedMeasurableAndLeavesRealCoverage()
    {
        var shape = new Regex("^[a-z][a-z0-9-]*$", RegexOptions.CultureInvariant);
        var perFamily = new SortedDictionary<string, (int Accepted, int Rejected)>(StringComparer.Ordinal);
        var reasons = new SortedDictionary<string, int>(StringComparer.Ordinal);

        foreach (var parameters in Stratified)
        {
            var execution = MetamorphicExecutor.Execute(MetamorphicTemplates.Build(parameters));
            var family = execution.Case.FamilyId;
            var counts = perFamily.GetValueOrDefault(family);

            if (execution.Accepted)
            {
                perFamily[family] = (counts.Accepted + 1, counts.Rejected);
                Assert.Equal("ok", execution.RejectionReason);
                continue;
            }

            perFamily[family] = (counts.Accepted, counts.Rejected + 1);
            var reason = execution.RejectionReason;
            reasons[reason] = reasons.GetValueOrDefault(reason) + 1;

            Assert.True(shape.IsMatch(reason), $"Rejection reason '{reason}' is not a stable kebab-case name.");
            Assert.True(reason.Length is > 3 and < 80, $"Rejection reason '{reason}' is not a usable name.");
            Assert.NotEqual("ok", reason);
        }

        // Every registered family must leave real coverage behind, or its rejection rule is
        // swallowing the family rather than declining a few inadmissible points.
        foreach (var definition in MetamorphicFamilyRegistry.All)
        {
            var counts = perFamily.GetValueOrDefault(definition.Id);
            Assert.True(
                counts.Accepted > 0,
                $"Family '{definition.Id}' produced no accepted case at all " +
                $"({counts.Rejected} rejected); it cannot contribute campaign coverage.");
        }

        // No single reason may account for the whole rejected population: that would mean one
        // precondition is doing all the work and the others are never exercised.
        var totalRejected = reasons.Values.Sum();
        if (totalRejected > 0)
        {
            Assert.True(
                reasons.Count > 1,
                "Every rejection in the stratified space has the same reason: " + reasons.Keys.First());
        }
    }

    /// <summary>
    /// Normalization is idempotent and encoding round-trips, for every family and for arbitrary
    /// bytes — the two properties <c>Decode(Encode(case))</c> stability rests on.
    /// </summary>
    [Fact]
    public void EveryFamilyNormalizer_IsIdempotentAndRoundTrips()
    {
        foreach (var parameters in Stratified)
        {
            var definition = parameters.Definition;
            var once = definition.Normalize(parameters);
            var twice = definition.Normalize(once);
            Assert.Equal(once, twice);
            Assert.Equal(parameters, once);
            Assert.Equal(parameters, MetamorphicDecoder.Decode(parameters.Encode()));
        }

        // Arbitrary bytes, not just canonical encodings: a decoder that normalized only its own
        // output would still let two campaign inputs mean the same case under two fingerprints.
        var payload = new byte[MetamorphicDecoder.MaxPayloadLength];
        for (var seed = 0; seed < 4096; seed++)
        {
            var state = (uint)(seed * 2654435761u + 1u);
            for (var i = 0; i < payload.Length; i++)
            {
                state = (state * 1664525u) + 1013904223u;
                payload[i] = (byte)(state >> 24);
            }

            var decoded = MetamorphicDecoder.Decode(payload);
            Assert.Equal(decoded, decoded.Definition.Normalize(decoded));
            Assert.Equal(decoded, MetamorphicDecoder.Decode(decoded.Encode()));
        }
    }

    // ── Observation purity ───────────────────────────────────────────────────

    /// <summary>
    /// The harness holds NO static mutable state.
    ///
    /// <para>Static state is the one way a run could influence the next through the measuring
    /// apparatus rather than through the runtime, which would make every isolation law it declares
    /// meaningless. Tables are allowed; a mutable collection or a settable static is not.</para>
    /// </summary>
    [Fact]
    public void TheHarness_HoldsNoStaticMutableState()
    {
        var mutable = new List<string>();
        var scanned = 0;

        var types = typeof(MetamorphicInvariants).Assembly
            .GetTypes()
            .Where(type => type.Namespace == "KatLang.ParserFuzz")
            .Where(type => type.Name.StartsWith("Metamorphic", StringComparison.Ordinal));

        foreach (var type in types)
        {
            scanned++;

            foreach (var field in type.GetFields(BindingFlags.Static | BindingFlags.Public | BindingFlags.NonPublic))
            {
                if (field.IsLiteral) continue;
                if (!field.IsInitOnly)
                {
                    mutable.Add($"{type.Name}.{field.Name} is a writable static field.");
                    continue;
                }

                if (IsMutableContainer(field.FieldType))
                    mutable.Add($"{type.Name}.{field.Name} is a readonly static holding mutable {field.FieldType.Name}.");
            }

            foreach (var property in type.GetProperties(BindingFlags.Static | BindingFlags.Public | BindingFlags.NonPublic))
            {
                if (property.SetMethod is not null)
                    mutable.Add($"{type.Name}.{property.Name} is a settable static property.");
            }
        }

        Assert.True(scanned > 20, $"Only {scanned} harness types were scanned; the filter is wrong.");
        Assert.True(mutable.Count == 0, "The harness holds static mutable state:\n  " + string.Join("\n  ", mutable));
    }

    private static bool IsMutableContainer(Type type)
    {
        if (type.IsArray) return true;
        if (!type.IsGenericType) return false;

        var name = type.GetGenericTypeDefinition().Name;
        return name.StartsWith("List`", StringComparison.Ordinal)
            || name.StartsWith("Dictionary`", StringComparison.Ordinal)
            || name.StartsWith("HashSet`", StringComparison.Ordinal)
            || name.StartsWith("Queue`", StringComparison.Ordinal)
            || name.StartsWith("Stack`", StringComparison.Ordinal)
            || name.StartsWith("SortedDictionary`", StringComparison.Ordinal);
    }

    /// <summary>
    /// A/A, A/B/A, and reversed execution over EVERY registered family: repeating a case, running
    /// an unrelated program between the two observations, and swapping which member is observed
    /// first must all produce the identical execution and the identical fingerprint.
    /// </summary>
    [Fact]
    public void EveryFamily_IsRepeatable_Isolated_AndOrderIndependent()
    {
        foreach (var parameters in OnePerFamily())
        {
            var testCase = MetamorphicTemplates.Build(parameters);
            var where = parameters.ToString();

            // A/A: the same case twice in one process.
            var first = MetamorphicExecutor.Execute(testCase);
            var second = MetamorphicExecutor.Execute(testCase);
            Assert.Equal(first.Accepted, second.Accepted);
            Assert.Equal(first.RejectionReason, second.RejectionReason);
            Assert.Equal(first.Left, second.Left);
            Assert.Equal(first.Right, second.Right);
            Assert.Equal(
                MetamorphicFingerprint.Describe(first, null),
                MetamorphicFingerprint.Describe(second, null));

            // A/B/A: an unrelated evaluation between them, under each side's REAL profile.
            MetamorphicExecutor.AssertIsolated(testCase.LeftSource, testCase.LeftProfile);
            MetamorphicExecutor.AssertIsolated(testCase.RightSource, testCase.RightProfile);
            var third = MetamorphicExecutor.Execute(testCase);
            Assert.Equal(first.Left, third.Left);
            Assert.Equal(first.Right, third.Right);

            // Reversed observation order: the members are still reported as left and right, so a
            // relation that only holds one way round is a leak rather than a policy.
            var reversed = MetamorphicExecutor.Execute(testCase with
            {
                ExecutionOrder = testCase.ExecutionOrder == MetamorphicExecutionOrder.LeftFirst
                    ? MetamorphicExecutionOrder.RightFirst
                    : MetamorphicExecutionOrder.LeftFirst,
            });

            Assert.True(reversed.Accepted == first.Accepted, $"{where}: acceptance depends on execution order.");
            if (!first.Accepted) continue;

            Assert.Equal(first.Left, reversed.Left);
            Assert.Equal(first.Right, reversed.Right);
            Assert.Null(MetamorphicComparator.Compare(testCase, reversed.Left!, reversed.Right!));
        }
    }

    // ── Replay integrity ─────────────────────────────────────────────────────

    /// <summary>
    /// A mismatch report reconstructs its case from the PAYLOAD ALONE — no local files, no
    /// process state, no corpus. The report is the only artifact a triage session starts from, so
    /// the payload it prints has to be sufficient on its own.
    /// </summary>
    [Fact]
    public void AMismatchReport_ReconstructsItsCaseFromThePayloadAlone()
    {
        var checkedCases = 0;

        foreach (var parameters in OnePerFamily())
        {
            var report = MetamorphicInvariants.Run(parameters.Encode());

            // Force a mismatch through a deliberately broken relation so the full report renders,
            // exactly as it would in a campaign.
            var broken = report.Execution.Case with
            {
                SemanticRelation = MetamorphicSemanticRelation.SemanticEqual,
                OperationalRelation = MetamorphicOperationalRelation.ExactObservedWorkEqual,
            };
            var mismatch = new MetamorphicMismatch(
                MetamorphicMismatchKind.EvaluationSteps, MetamorphicMismatchClass.Operational, "audit", "1", "2");
            var text = MetamorphicInvariants.Describe(report with { Execution = report.Execution with { Case = broken } }, mismatch);

            var hex = parameters.ToHex();
            Assert.Contains(hex, text, StringComparison.Ordinal);
            Assert.Contains(
                "metamorphic-replay --payload " + hex.Replace(" ", "", StringComparison.Ordinal),
                text,
                StringComparison.Ordinal);

            // Rebuild strictly from the printed hex, as a triage session would.
            var bytes = hex.Split(' ').Select(part => Convert.ToByte(part, 16)).ToArray();
            var rebuilt = MetamorphicTemplates.Build(MetamorphicDecoder.Decode(bytes));
            var original = report.Execution.Case;

            Assert.Equal(original.Family, rebuilt.Family);
            Assert.Equal(original.Parameters, rebuilt.Parameters);
            Assert.Equal(original.LeftSource, rebuilt.LeftSource);
            Assert.Equal(original.RightSource, rebuilt.RightSource);
            Assert.Equal(original.SemanticRelation, rebuilt.SemanticRelation);
            Assert.Equal(original.OperationalRelation, rebuilt.OperationalRelation);
            Assert.Equal(original.LeftProfile.ToString(), rebuilt.LeftProfile.ToString());
            Assert.Equal(original.RightProfile.ToString(), rebuilt.RightProfile.ToString());
            Assert.Equal(original.RunPlan, rebuilt.RunPlan);
            Assert.Equal(original.ExecutionOrder, rebuilt.ExecutionOrder);
            Assert.Equal(original.BoundaryStop, rebuilt.BoundaryStop);
            Assert.Equal(original.Precondition, rebuilt.Precondition);
            checkedCases++;
        }

        Assert.Equal(MetamorphicFamilyRegistry.All.Length, checkedCases);
    }

    // ── Fingerprint audit ────────────────────────────────────────────────────

    /// <summary>
    /// Across the WHOLE stratified space, two different normalized parameter points never share a
    /// fingerprint.
    ///
    /// <para>Fingerprints are compared here on the CASE, with a synthetic unexecuted execution, so
    /// the check covers every case-derived dimension — family, template variant, limits, both
    /// execution profiles, run plan, order, boundary stop, declared relations — over the complete
    /// space rather than a sample. The observation-derived features are covered by the Phase 3
    /// suite, which executes.</para>
    /// </summary>
    [Fact]
    public void CaseFingerprints_NeverCollideAcrossTheWholeStratifiedSpace()
    {
        var byFingerprint = new Dictionary<string, MetamorphicParameters>(StringComparer.Ordinal);
        var collisions = new List<string>();

        foreach (var parameters in Stratified)
        {
            var testCase = MetamorphicTemplates.Build(parameters);
            var synthetic = new MetamorphicExecution(testCase, false, "audit", null, null);
            var fingerprint = MetamorphicFingerprint.Describe(synthetic, null);

            if (byFingerprint.TryGetValue(fingerprint, out var other) && !other.Equals(parameters))
                collisions.Add($"{other} AND {parameters} share:\n    {fingerprint}");
            else byFingerprint[fingerprint] = parameters;
        }

        Assert.True(
            collisions.Count == 0,
            $"{collisions.Count} distinct parameter point(s) share a fingerprint:\n  " +
            string.Join("\n  ", collisions.Take(5)));

        Assert.Equal(Stratified.Count, byFingerprint.Count);
    }

    /// <summary>
    /// No fingerprint anywhere in the space carries a value that could differ between two runs of
    /// the same input: a thread or process id, an object hash, an address, a timing, or raw source
    /// text.
    /// </summary>
    [Fact]
    public void Fingerprints_CarryNothingThatCouldDifferBetweenRuns()
    {
        string[] forbidden =
        [
            "threadid", "managedthread", "processid", "elapsed", "ticks", "hashcode",
            "@0x", "system.", "0x0000", "\n",
        ];

        foreach (var parameters in OnePerFamily())
        {
            var execution = MetamorphicExecutor.Execute(MetamorphicTemplates.Build(parameters));
            var fingerprint = MetamorphicFingerprint.Describe(execution, null);
            var lowered = fingerprint.ToLowerInvariant();

            foreach (var token in forbidden)
            {
                Assert.False(
                    lowered.Contains(token, StringComparison.Ordinal),
                    $"Fingerprint for {parameters} contains unstable token '{token}':\n  {fingerprint}");
            }

            // The fingerprint must not embed the generated program text: a template is identified
            // far more stably by its decoded dimensions than by the source it happens to emit.
            foreach (var line in execution.Case.LeftSource.Split('\n'))
            {
                if (line.Length >= 8)
                    Assert.DoesNotContain(line, fingerprint, StringComparison.Ordinal);
            }

            Assert.Equal(fingerprint, MetamorphicFingerprint.Describe(execution, null));
        }
    }

    // ── Bounds ───────────────────────────────────────────────────────────────

    /// <summary>
    /// Nothing a payload selects grows with an encoded integer: generated sources, expected
    /// totals, configured limits, the bounded search, and the isolation thread count are all
    /// bounded by fixed harness constants.
    /// </summary>
    [Fact]
    public void EveryDecodedCase_StaysInsideFixedStructuralBounds()
    {
        const int maxSourceChars = 4096;
        const long maxExpectedItems = 100_000;

        var longestSource = 0;
        var largestItemTotal = 0L;

        foreach (var parameters in Stratified)
        {
            var testCase = MetamorphicTemplates.Build(parameters);
            longestSource = Math.Max(longestSource, Math.Max(testCase.LeftSource.Length, testCase.RightSource.Length));
            largestItemTotal = Math.Max(largestItemTotal, testCase.ExpectedItemTotal);

            Assert.True(
                testCase.LeftSource.Length <= maxSourceChars && testCase.RightSource.Length <= maxSourceChars,
                $"{parameters} generates a source of {Math.Max(testCase.LeftSource.Length, testCase.RightSource.Length)} chars.");
            Assert.True(
                testCase.ExpectedItemTotal <= maxExpectedItems,
                $"{parameters} expects {testCase.ExpectedItemTotal} materialized items.");
            Assert.True(parameters.Encode().Length <= MetamorphicDecoder.MaxPayloadLength);
        }

        // The fixed constants the campaign's worst case depends on.
        Assert.Equal(4, MetamorphicExecutor.ParallelTaskCount);
        Assert.Equal(3, MetamorphicExecutor.InterleavedRunCount);
        Assert.Equal(32, MetamorphicBoundaryPolicy.MaxSearchProbes);
        Assert.Equal(10, MetamorphicDecoder.MaxPayloadLength);

        // A bounded search must be able to resolve its whole interval inside its probe budget,
        // or the boundary it reports depends on where the budget ran out.
        foreach (var definition in MetamorphicBoundaryPolicy.SearchedDimensions)
        {
            var interval = MetamorphicBoundaryPolicy.IntervalOf(definition.Dimension);
            var needed = (2 * (int)Math.Ceiling(Math.Log2(interval.Count))) + 2;
            Assert.True(
                needed <= MetamorphicBoundaryPolicy.MaxSearchProbes,
                $"{interval} needs about {needed} probes but the budget is {MetamorphicBoundaryPolicy.MaxSearchProbes}.");
        }

        Assert.True(longestSource > 100, "The stratified space generates only trivial sources.");
        Assert.True(largestItemTotal > 0, "No case in the stratified space materializes anything.");
    }
}
