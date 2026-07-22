using System.Globalization;

namespace KatLang.ParserFuzz;

/// <summary>Which declared relation a mismatch violated.</summary>
internal enum MetamorphicMismatchClass
{
    /// <summary>The language-semantic relation (what the program means).</summary>
    Semantic,

    /// <summary>The resource-limit verdict (host policy: did the run stop for a budget?).</summary>
    ResourceBoundary,

    /// <summary>The operational relation (how much work the run charged).</summary>
    Operational,

    /// <summary>The rendering surface (returned display text and its strict length bound).</summary>
    Rendering,

    /// <summary>Two independent executions were distinguishable — run state leaked.</summary>
    StateIsolation,
}

/// <summary>The exact comparison that failed. One kind per compared field, so a diagnostic
/// can name the property rather than dumping two opaque observations.</summary>
internal enum MetamorphicMismatchKind
{
    SemanticOutcome,
    ResourceLimitVerdict,
    SemanticErrorCategory,
    SemanticErrorPayload,
    SemanticStructure,
    EmittedCount,
    MaterializedItems,
    MaterializedStringChars,
    EvaluationSteps,
    PeakDynamicDepth,

    // ── Phase 3 ──────────────────────────────────────────────────────────────
    HostAtoms,
    TopLevelProperty,
    RenderedText,
    RenderedLength,

    /// <summary>A larger effective limit turned a success into a non-success.</summary>
    MonotonicRegression,

    /// <summary>The boundary case's left member did not succeed AT the derived boundary.</summary>
    BoundarySuccess,

    /// <summary>One unit below the boundary did not stop the way the case declared.</summary>
    BoundaryStopKind,

    /// <summary>Two independent runs of the same program were distinguishable.</summary>
    IndependentRunState,
}

/// <summary>One failed comparison, with the two values that failed it.</summary>
internal sealed record MetamorphicMismatch(
    MetamorphicMismatchKind Kind,
    MetamorphicMismatchClass Class,
    string ComparedProperty,
    string LeftValue,
    string RightValue)
{
    public string Headline =>
        $"{Class} relation violated on {ComparedProperty}: left={LeftValue} right={RightValue}";
}

/// <summary>
/// Compares one executed pair against the relations its case DECLARED.
///
/// <para>The order is chosen so the reported kind is the most specific true statement about
/// the difference: an ok/err split is an outcome mismatch, two errors that differ only in
/// whether a resource budget stopped them is a resource-boundary mismatch, and only once the
/// semantic halves agree do the operational counters get the blame.</para>
///
/// <para><b>Operational counters are compared only when both executions complete.</b> When
/// either side stops at a structured resource limit, semantic outcome, resource-limit kind, and
/// structured payload remain comparable, but partial work counters are not
/// (<see cref="WorkIsComparable"/>). An ordinary, non-resource semantic failure is not exempt:
/// its counters are compared exactly like a successful run's. Phase 3 adds one more gate for the
/// same reason: a surface that never hands back a budget cannot contribute counters at all, so a
/// pair including one declares <see cref="MetamorphicOperationalRelation.NotCompared"/> rather
/// than comparing two zeroes.</para>
/// </summary>
internal static class MetamorphicComparator
{
    /// <summary>Returns the first violated comparison, or <c>null</c> when every declared relation holds.</summary>
    internal static MetamorphicMismatch? Compare(
        MetamorphicCase testCase,
        MetamorphicOperationalObservation left,
        MetamorphicOperationalObservation right)
    {
        ArgumentNullException.ThrowIfNull(testCase);
        ArgumentNullException.ThrowIfNull(left);
        ArgumentNullException.ThrowIfNull(right);

        // The strict rendering bound is a per-SIDE law, not a pair relation: whatever the two
        // members are compared on, a surface that returned more UTF-16 units than its configured
        // display limit allows has already broken its contract.
        if (RenderedLengthViolation(left, "left") is { } leftBound) return leftBound;
        if (RenderedLengthViolation(right, "right") is { } rightBound) return rightBound;

        var semantic = testCase.SemanticRelation switch
        {
            MetamorphicSemanticRelation.SemanticEqual => CompareSemanticEqual(left.Semantic, right.Semantic),
            MetamorphicSemanticRelation.SameStructuredOutcome => CompareSharedFacets(left, right),
            MetamorphicSemanticRelation.MonotonicSuccess => CompareMonotonicSuccess(left, right),
            MetamorphicSemanticRelation.SameResourceBoundary => CompareResourceBoundary(testCase, left, right),
            MetamorphicSemanticRelation.IndependentRunStable => CompareIndependentRunStable(left, right),
            _ => throw new MetamorphicHarnessException(
                $"No comparison is implemented for semantic relation {testCase.SemanticRelation}."),
        };

        if (semantic is not null) return semantic;

        // Operational counters are only meaningful for runs that COMPLETED. When a resource
        // limit stops a run, its counters are a PARTIAL PREFIX recorded at the abort point, and
        // two equivalent forms may legitimately have done different preparatory work before
        // reaching the same limit — `reduce(R, contains, [1, 2])` materializes its initial
        // accumulator before forcing R, while `R.reduce(contains, [1, 2])` prepares the receiver
        // first and fails earlier. The semantic relation above has already established that both
        // sides report the same error kind and the same structured payload, which is what a
        // program can actually observe; measured over the whole builtin x receiver x
        // (item budget x string budget) grid, no observable outcome ever differed, and no pair of
        // SUCCESSFUL runs ever differed on counters.
        if (!WorkIsComparable(left, right)) return null;

        return testCase.OperationalRelation switch
        {
            MetamorphicOperationalRelation.NotCompared => null,
            MetamorphicOperationalRelation.ExactMaterializationEqual => CompareExactMaterializationEqual(left, right),
            MetamorphicOperationalRelation.ExactObservedWorkEqual =>
                CompareExactMaterializationEqual(left, right) ?? CompareObservedWork(left, right),
            MetamorphicOperationalRelation.MaterializationNeverIncreases =>
                CompareMaterializationNeverIncreases(left, right),
            MetamorphicOperationalRelation.WorkNeverIncreases => CompareWorkNeverIncreases(left, right),
            MetamorphicOperationalRelation.IdenticalWork =>
                CompareExactMaterializationEqual(left, right)
                ?? CompareObservedWork(left, right)
                ?? CompareEvidence(left, right),
            _ => throw new MetamorphicHarnessException(
                $"No comparison is implemented for operational relation {testCase.OperationalRelation}."),
        };
    }

    /// <summary>
    /// True when both runs finished under their budgets AND both surfaces actually report
    /// counters, so the numbers describe the WHOLE work each form performed rather than the
    /// prefix that happened to precede an abort — or nothing at all.
    /// </summary>
    internal static bool WorkIsComparable(
        MetamorphicOperationalObservation left, MetamorphicOperationalObservation right)
        => !left.Semantic.IsResourceLimit
            && !right.Semantic.IsResourceLimit
            && left.Facets.HasFlag(MetamorphicFacets.OperationalCounters)
            && right.Facets.HasFlag(MetamorphicFacets.OperationalCounters);

    // ── Semantic relations ───────────────────────────────────────────────────

    private static MetamorphicMismatch? CompareSemanticEqual(
        MetamorphicSemanticObservation left, MetamorphicSemanticObservation right)
    {
        if (!string.Equals(left.Outcome, right.Outcome, StringComparison.Ordinal))
        {
            return new MetamorphicMismatch(
                MetamorphicMismatchKind.SemanticOutcome, MetamorphicMismatchClass.Semantic,
                "success/failure outcome", left.Outcome, right.Outcome);
        }

        // A resource-limit stop is host policy, not a language-semantic fact, so it is kept
        // distinguishable from an ordinary semantic failure with its own mismatch kind.
        if (left.IsResourceLimit != right.IsResourceLimit)
        {
            return new MetamorphicMismatch(
                MetamorphicMismatchKind.ResourceLimitVerdict, MetamorphicMismatchClass.ResourceBoundary,
                "resource-limit verdict", Flag(left.IsResourceLimit), Flag(right.IsResourceLimit));
        }

        if (!string.Equals(left.ErrorCategory, right.ErrorCategory, StringComparison.Ordinal))
        {
            return new MetamorphicMismatch(
                MetamorphicMismatchKind.SemanticErrorCategory,
                left.IsResourceLimit ? MetamorphicMismatchClass.ResourceBoundary : MetamorphicMismatchClass.Semantic,
                "innermost error kind", Text(left.ErrorCategory), Text(right.ErrorCategory));
        }

        if (!string.Equals(left.ErrorPayload, right.ErrorPayload, StringComparison.Ordinal))
        {
            return new MetamorphicMismatch(
                MetamorphicMismatchKind.SemanticErrorPayload,
                left.IsResourceLimit ? MetamorphicMismatchClass.ResourceBoundary : MetamorphicMismatchClass.Semantic,
                "structured error payload", Text(left.ErrorPayload), Text(right.ErrorPayload));
        }

        if (!string.Equals(left.Structure, right.Structure, StringComparison.Ordinal))
        {
            return new MetamorphicMismatch(
                MetamorphicMismatchKind.SemanticStructure, MetamorphicMismatchClass.Semantic,
                "neutral structural value", Text(left.Structure), Text(right.Structure));
        }

        if (left.EmittedCount != right.EmittedCount)
        {
            return new MetamorphicMismatch(
                MetamorphicMismatchKind.EmittedCount, MetamorphicMismatchClass.Semantic,
                "emitted count", Number(left.EmittedCount), Number(right.EmittedCount));
        }

        return null;
    }

    /// <summary>
    /// Entry-point parity: compare every facet BOTH surfaces project, and nothing else.
    ///
    /// <para>The intersection is the whole point. <c>Evaluator.Run</c> has no emitted count and
    /// <c>RunFlat</c> has no structural value, so comparing those fields would be comparing two
    /// absences. The registry refuses to register a pair whose intersection is only the outcome,
    /// so this can never pass vacuously.</para>
    /// </summary>
    private static MetamorphicMismatch? CompareSharedFacets(
        MetamorphicOperationalObservation left, MetamorphicOperationalObservation right)
    {
        var shared = left.Facets & right.Facets;

        if (!string.Equals(left.Semantic.Outcome, right.Semantic.Outcome, StringComparison.Ordinal))
        {
            return new MetamorphicMismatch(
                MetamorphicMismatchKind.SemanticOutcome, MetamorphicMismatchClass.Semantic,
                "success/failure outcome", left.Semantic.Outcome, right.Semantic.Outcome);
        }

        if (shared.HasFlag(MetamorphicFacets.StructuredError)
            && CompareStructuredError(left.Semantic, right.Semantic) is { } structuredError)
        {
            return structuredError;
        }

        if (shared.HasFlag(MetamorphicFacets.Structure)
            && !string.Equals(left.Semantic.Structure, right.Semantic.Structure, StringComparison.Ordinal))
        {
            return new MetamorphicMismatch(
                MetamorphicMismatchKind.SemanticStructure, MetamorphicMismatchClass.Semantic,
                "neutral structural value", Text(left.Semantic.Structure), Text(right.Semantic.Structure));
        }

        if (shared.HasFlag(MetamorphicFacets.EmittedCount) && left.Semantic.EmittedCount != right.Semantic.EmittedCount)
        {
            return new MetamorphicMismatch(
                MetamorphicMismatchKind.EmittedCount, MetamorphicMismatchClass.Semantic,
                "emitted count", Number(left.Semantic.EmittedCount), Number(right.Semantic.EmittedCount));
        }

        if (shared.HasFlag(MetamorphicFacets.HostAtoms)
            && !string.Equals(left.Projection?.HostAtoms, right.Projection?.HostAtoms, StringComparison.Ordinal))
        {
            return new MetamorphicMismatch(
                MetamorphicMismatchKind.HostAtoms, MetamorphicMismatchClass.Semantic,
                "host-atom projection", Text(left.Projection?.HostAtoms), Text(right.Projection?.HostAtoms));
        }

        if (shared.HasFlag(MetamorphicFacets.TopLevelProperty)
            && !string.Equals(left.Projection?.TopLevelProperty, right.Projection?.TopLevelProperty, StringComparison.Ordinal))
        {
            return new MetamorphicMismatch(
                MetamorphicMismatchKind.TopLevelProperty, MetamorphicMismatchClass.Semantic,
                "top-level property channel",
                Text(left.Projection?.TopLevelProperty), Text(right.Projection?.TopLevelProperty));
        }

        return shared.HasFlag(MetamorphicFacets.RenderedText) ? CompareRenderedText(left, right) : null;
    }

    private static MetamorphicMismatch? CompareStructuredError(
        MetamorphicSemanticObservation left, MetamorphicSemanticObservation right)
    {
        if (left.IsResourceLimit != right.IsResourceLimit)
        {
            return new MetamorphicMismatch(
                MetamorphicMismatchKind.ResourceLimitVerdict, MetamorphicMismatchClass.ResourceBoundary,
                "resource-limit verdict", Flag(left.IsResourceLimit), Flag(right.IsResourceLimit));
        }

        if (!string.Equals(left.ErrorCategory, right.ErrorCategory, StringComparison.Ordinal))
        {
            return new MetamorphicMismatch(
                MetamorphicMismatchKind.SemanticErrorCategory,
                left.IsResourceLimit ? MetamorphicMismatchClass.ResourceBoundary : MetamorphicMismatchClass.Semantic,
                "innermost error kind", Text(left.ErrorCategory), Text(right.ErrorCategory));
        }

        return string.Equals(left.ErrorPayload, right.ErrorPayload, StringComparison.Ordinal)
            ? null
            : new MetamorphicMismatch(
                MetamorphicMismatchKind.SemanticErrorPayload,
                left.IsResourceLimit ? MetamorphicMismatchClass.ResourceBoundary : MetamorphicMismatchClass.Semantic,
                "structured error payload", Text(left.ErrorPayload), Text(right.ErrorPayload));
    }

    /// <summary>
    /// Rendered text is required to be EXACTLY equal only where the two surfaces produced the
    /// same rendering PROJECTION.
    ///
    /// <para>That qualification is a documented API fact, not a weakening:
    /// <c>KatLangEngine.EvaluateToString</c> returns space-joined host atoms on success and the
    /// structured diagnostic rendering otherwise, so it is equal to
    /// <c>Run(...).ToDisplayString()</c> on every failure and deliberately different on success.
    /// Requiring equality across different projections would assert something the runtime never
    /// promised; the strict length bound is checked on both sides regardless.</para>
    /// </summary>
    private static MetamorphicMismatch? CompareRenderedText(
        MetamorphicOperationalObservation left, MetamorphicOperationalObservation right)
    {
        var leftProjection = left.Projection;
        var rightProjection = right.Projection;
        if (leftProjection is null || rightProjection is null) return null;

        if (!string.Equals(leftProjection.RenderedProjection, rightProjection.RenderedProjection, StringComparison.Ordinal))
            return null;

        return string.Equals(leftProjection.RenderedText, rightProjection.RenderedText, StringComparison.Ordinal)
            ? null
            : new MetamorphicMismatch(
                MetamorphicMismatchKind.RenderedText, MetamorphicMismatchClass.Rendering,
                $"rendered text ({leftProjection.RenderedProjection})",
                Quote(leftProjection.RenderedText), Quote(rightProjection.RenderedText));
    }

    /// <summary>The per-side law: a rendering surface must never return more units than its limit.</summary>
    private static MetamorphicMismatch? RenderedLengthViolation(
        MetamorphicOperationalObservation observation, string side)
    {
        if (!observation.Facets.HasFlag(MetamorphicFacets.RenderedText)) return null;
        if (observation.Projection is not { RenderedText: not null } projection) return null;
        if (projection.RenderedLength <= projection.RenderedLimit) return null;

        return new MetamorphicMismatch(
            MetamorphicMismatchKind.RenderedLength, MetamorphicMismatchClass.Rendering,
            $"{side} rendered length within its configured display limit",
            Number(projection.RenderedLength), Number(projection.RenderedLimit));
    }

    /// <summary>
    /// Monotonic success: a LARGER effective limit may never turn a success into a non-success,
    /// and where it still succeeds it must produce the same observation. A left member that did
    /// not succeed places no obligation at all — that is what makes this a monotonicity law
    /// rather than an equality, and why a boundary sweep can safely include limits below the
    /// requirement.
    /// </summary>
    private static MetamorphicMismatch? CompareMonotonicSuccess(
        MetamorphicOperationalObservation left, MetamorphicOperationalObservation right)
    {
        if (left.Semantic.Outcome != "ok") return null;

        if (right.Semantic.Outcome != "ok")
        {
            return new MetamorphicMismatch(
                MetamorphicMismatchKind.MonotonicRegression, MetamorphicMismatchClass.ResourceBoundary,
                "a larger effective limit still succeeding",
                "ok", "err:" + Text(right.Semantic.ErrorCategory));
        }

        return CompareSharedFacets(left, right);
    }

    /// <summary>
    /// The exact boundary law: at the derived boundary the program must succeed, and one unit
    /// below it must stop in the way the case declared. Both the stop kind and the expected
    /// structured error come from the case, so a new resource dimension adds DATA rather than a
    /// comparator branch.
    /// </summary>
    private static MetamorphicMismatch? CompareResourceBoundary(
        MetamorphicCase testCase,
        MetamorphicOperationalObservation left,
        MetamorphicOperationalObservation right)
    {
        if (left.Semantic.Outcome != "ok")
        {
            return new MetamorphicMismatch(
                MetamorphicMismatchKind.BoundarySuccess, MetamorphicMismatchClass.ResourceBoundary,
                "success exactly at the derived boundary",
                "err:" + Text(left.Semantic.ErrorCategory), "expected ok");
        }

        switch (testCase.BoundaryStop)
        {
            case MetamorphicBoundaryStop.ResourceError:
            {
                var expected = testCase.ExpectedResourceKind ?? "(unspecified)";
                if (right.Semantic.Outcome == "ok" || !right.Semantic.IsResourceLimit)
                {
                    return new MetamorphicMismatch(
                        MetamorphicMismatchKind.BoundaryStopKind, MetamorphicMismatchClass.ResourceBoundary,
                        "one unit below the boundary stopping with a resource error",
                        expected,
                        right.Semantic.Outcome == "ok" ? "ok" : "semantic:" + Text(right.Semantic.ErrorCategory));
                }

                return string.Equals(right.Semantic.ErrorCategory, expected, StringComparison.Ordinal)
                    ? null
                    : new MetamorphicMismatch(
                        MetamorphicMismatchKind.BoundaryStopKind, MetamorphicMismatchClass.ResourceBoundary,
                        "the resource error the dimension enforces",
                        expected, Text(right.Semantic.ErrorCategory));
            }

            case MetamorphicBoundaryStop.RenderingTruncation:
            {
                // Display length is a host RENDERING policy, not an evaluation budget: the run
                // still succeeds and the writer returns a complete bounded overflow indication.
                if (right.Semantic.Outcome != "ok")
                {
                    return new MetamorphicMismatch(
                        MetamorphicMismatchKind.BoundaryStopKind, MetamorphicMismatchClass.Rendering,
                        "a lower display limit bounding the rendering without failing the run",
                        "ok", "err:" + Text(right.Semantic.ErrorCategory));
                }

                var leftText = left.Projection?.RenderedText;
                var rightText = right.Projection?.RenderedText;
                return string.Equals(leftText, rightText, StringComparison.Ordinal)
                    ? new MetamorphicMismatch(
                        MetamorphicMismatchKind.BoundaryStopKind, MetamorphicMismatchClass.Rendering,
                        "a lower display limit changing the rendered text",
                        Quote(leftText), Quote(rightText))
                    : null;
            }

            default:
                throw new MetamorphicHarnessException(
                    $"A SameResourceBoundary case must declare a boundary stop; this one declared {testCase.BoundaryStop}.");
        }
    }

    /// <summary>
    /// Two INDEPENDENT executions of the same program under the same policy must be
    /// indistinguishable in every recorded respect. Any difference at all means run state — a
    /// counter, a cache, an optimizer decision, a diagnostic — survived across a run boundary.
    /// </summary>
    private static MetamorphicMismatch? CompareIndependentRunStable(
        MetamorphicOperationalObservation left, MetamorphicOperationalObservation right)
    {
        if (CompareSemanticEqual(left.Semantic, right.Semantic) is { } semantic)
            return semantic with { Class = MetamorphicMismatchClass.StateIsolation };

        if (CompareSharedFacets(left, right) is { } facets)
            return facets with { Class = MetamorphicMismatchClass.StateIsolation };

        if (CompareExactMaterializationEqual(left, right) is { } materialization)
            return materialization with { Class = MetamorphicMismatchClass.StateIsolation };

        if (CompareObservedWork(left, right) is { } work)
            return work with { Class = MetamorphicMismatchClass.StateIsolation };

        return left == right
            ? null
            : new MetamorphicMismatch(
                MetamorphicMismatchKind.IndependentRunState, MetamorphicMismatchClass.StateIsolation,
                "complete observation of two independent runs", left.ToString(), right.ToString());
    }

    // ── Operational relations ────────────────────────────────────────────────

    /// <summary>
    /// Exact equality of what the two runs MATERIALIZED. Evaluation steps and peak dynamic
    /// depth are deliberately not compared: they are carried on the observation for
    /// diagnostics, but Phase 1 claims only that the two spellings of one call construct the
    /// same collection storage, which is the claim the repository's dotted-receiver contract
    /// actually establishes.
    /// </summary>
    private static MetamorphicMismatch? CompareExactMaterializationEqual(
        MetamorphicOperationalObservation left, MetamorphicOperationalObservation right)
    {
        if (left.MaterializedItems != right.MaterializedItems)
        {
            return new MetamorphicMismatch(
                MetamorphicMismatchKind.MaterializedItems, MetamorphicMismatchClass.Operational,
                "materialized collection-item slots", Number(left.MaterializedItems), Number(right.MaterializedItems));
        }

        if (left.MaterializedStringChars != right.MaterializedStringChars)
        {
            return new MetamorphicMismatch(
                MetamorphicMismatchKind.MaterializedStringChars, MetamorphicMismatchClass.Operational,
                "materialized string UTF-16 units",
                Number(left.MaterializedStringChars), Number(right.MaterializedStringChars));
        }

        return null;
    }

    /// <summary>
    /// The DIRECTIONAL materialization relation: the right member may charge less (it is the
    /// fusion-eligible spelling) but never more. Doing more work than the equivalent ordinary
    /// form is never a legitimate implementation choice.
    /// </summary>
    private static MetamorphicMismatch? CompareMaterializationNeverIncreases(
        MetamorphicOperationalObservation left, MetamorphicOperationalObservation right)
    {
        if (right.MaterializedItems > left.MaterializedItems)
        {
            return new MetamorphicMismatch(
                MetamorphicMismatchKind.MaterializedItems, MetamorphicMismatchClass.Operational,
                "materialized collection-item slots (right must never exceed left)",
                Number(left.MaterializedItems), Number(right.MaterializedItems));
        }

        if (right.MaterializedStringChars > left.MaterializedStringChars)
        {
            return new MetamorphicMismatch(
                MetamorphicMismatchKind.MaterializedStringChars, MetamorphicMismatchClass.Operational,
                "materialized string UTF-16 units (right must never exceed left)",
                Number(left.MaterializedStringChars), Number(right.MaterializedStringChars));
        }

        return null;
    }

    /// <summary>
    /// The Phase 3 directional relation, in the opposite direction from
    /// <see cref="CompareMaterializationNeverIncreases"/> because the member permitted to do
    /// less is the LEFT one: an optimized run against the generic run of the same source, and a
    /// cached-property run against the rebuilt form.
    ///
    /// <para>Steps are included — an optimizer and a cache both exist to perform less work, and
    /// "the optimized run took more steps than the generic one" is never a legitimate
    /// implementation choice. Peak dynamic depth is NOT included: an optimized loop plan reaches
    /// a different nesting profile than the generic interpreter by design, so it is recorded and
    /// reported but never a failure condition.</para>
    /// </summary>
    private static MetamorphicMismatch? CompareWorkNeverIncreases(
        MetamorphicOperationalObservation left, MetamorphicOperationalObservation right)
    {
        if (left.MaterializedItems > right.MaterializedItems)
        {
            return new MetamorphicMismatch(
                MetamorphicMismatchKind.MaterializedItems, MetamorphicMismatchClass.Operational,
                "materialized collection-item slots (left must never exceed right)",
                Number(left.MaterializedItems), Number(right.MaterializedItems));
        }

        if (left.MaterializedStringChars > right.MaterializedStringChars)
        {
            return new MetamorphicMismatch(
                MetamorphicMismatchKind.MaterializedStringChars, MetamorphicMismatchClass.Operational,
                "materialized string UTF-16 units (left must never exceed right)",
                Number(left.MaterializedStringChars), Number(right.MaterializedStringChars));
        }

        return left.EvaluationSteps <= right.EvaluationSteps
            ? null
            : new MetamorphicMismatch(
                MetamorphicMismatchKind.EvaluationSteps, MetamorphicMismatchClass.Operational,
                "evaluation steps (left must never exceed right)",
                Number(left.EvaluationSteps), Number(right.EvaluationSteps));
    }

    /// <summary>
    /// The additional counters an EXACT-WORK family claims. Declared only where the two members
    /// resolve to the same invocations, so a difference here means one form performed work the
    /// other did not — never a legitimate implementation choice.
    /// </summary>
    private static MetamorphicMismatch? CompareObservedWork(
        MetamorphicOperationalObservation left, MetamorphicOperationalObservation right)
    {
        if (left.EvaluationSteps != right.EvaluationSteps)
        {
            return new MetamorphicMismatch(
                MetamorphicMismatchKind.EvaluationSteps, MetamorphicMismatchClass.Operational,
                "evaluation steps", Number(left.EvaluationSteps), Number(right.EvaluationSteps));
        }

        if (left.PeakDynamicDepth != right.PeakDynamicDepth)
        {
            return new MetamorphicMismatch(
                MetamorphicMismatchKind.PeakDynamicDepth, MetamorphicMismatchClass.Operational,
                "peak dynamic depth", Number(left.PeakDynamicDepth), Number(right.PeakDynamicDepth));
        }

        return null;
    }

    /// <summary>
    /// The optimizer and cache evidence an IDENTICAL-WORK relation additionally claims.
    ///
    /// <para>This is how in-budget neutrality proves what it says it proves: a limit that never
    /// binds must not have switched an optimizer off. Comparing steps alone would usually catch
    /// that, but not always — a fused pipeline and a generic one can charge the same steps while
    /// materializing differently — so the recorded execution PATH is compared directly. Evidence
    /// is only collected when the case asked for it; two absent profiles compare equal, which is
    /// correct for the families that make no evidence claim.</para>
    /// </summary>
    private static MetamorphicMismatch? CompareEvidence(
        MetamorphicOperationalObservation left, MetamorphicOperationalObservation right)
    {
        if (left.OptimizerEvidence is { } leftOptimizer
            && right.OptimizerEvidence is { } rightOptimizer
            && leftOptimizer != rightOptimizer)
        {
            return new MetamorphicMismatch(
                MetamorphicMismatchKind.IndependentRunState, MetamorphicMismatchClass.Operational,
                "optimizer execution path", leftOptimizer.ToString(), rightOptimizer.ToString());
        }

        return left.CacheEvidence is { } leftCache && right.CacheEvidence is { } rightCache && leftCache != rightCache
            ? new MetamorphicMismatch(
                MetamorphicMismatchKind.IndependentRunState, MetamorphicMismatchClass.Operational,
                "zero-argument property cache profile", leftCache.ToString(), rightCache.ToString())
            : null;
    }

    private static string Flag(bool value) => value ? "resource-limit" : "language-semantic";

    private static string Text(string? value) => value ?? "-";

    private static string Quote(string? value)
        => value is null ? "-" : "'" + value.Replace("\r", "\\r", StringComparison.Ordinal)
            .Replace("\n", "\\n", StringComparison.Ordinal) + "'";

    private static string Number(long value) => value.ToString(CultureInfo.InvariantCulture);

    private static string Number(int value) => value.ToString(CultureInfo.InvariantCulture);

    private static string Number(int? value) => value?.ToString(CultureInfo.InvariantCulture) ?? "-";
}
