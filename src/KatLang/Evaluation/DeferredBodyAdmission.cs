namespace KatLang.Evaluation;

/// <summary>
/// [HOST] B2c — the evaluator's STRUCTURAL ADMISSION of materialized deferred module bodies, owned
/// by one run (<see cref="EvaluationBudget.AdmitDeferredBody"/>).
///
/// <para><b>Why.</b> A run admits its program with the evaluator-weighted preflight
/// (<see cref="AstConsumerProfile.EvaluatorIterativeJoinSpines"/> at the run's effective
/// <see cref="EvaluationLimits.MaxAstDepth"/>) before evaluating anything, but a deferred region's
/// modules are unknown then: the walk sees only the placeholder. Materialization gates the loaded
/// body with the FRONT END's ceilings (<see cref="AstConsumerProfile.FullyRecursive"/>, judged
/// against the loader's unweighted traversal depth) — protection for elaboration, not for the
/// evaluator, which charges dot-call links and join re-entries more and may run under a lower
/// configured limit. So every materialized body is admitted here, by the run that consumes it,
/// before the evaluator descends into it.</para>
///
/// <para><b>What is judged.</b> The tree ordinary admission would have judged had the body been
/// present: the body at the position of its placeholder. The run's admitted root yields the
/// weighted prefix of every reachable placeholder (deepest occurrence;
/// <see cref="AstStructuralPreflight.AccumulateDeferredRegionPrefixes"/>), and the body passes the
/// one structural preflight at the limit minus that prefix — the same weights, sharing and cycle
/// rules and rejection positions. The materialized root's old Parent is excluded: both consumers
/// replace it before use, and the placeholder's attached parent was already judged at this position.
/// An admitted body contributes the prefixes of its own nested regions (its prefix plus their
/// depth within it), retaining deepest node arrivals across bodies. A region whose recorded prefix
/// grows after its body was admitted (a nested region reached through a second, deeper materialized body) is judged again
/// at the deeper prefix on its next consumption; no path can consume a region before every body
/// enclosing that path has been admitted, because the evaluator descends into a body only through
/// this gate.</para>
///
/// <para><b>Ownership and caching.</b> Everything here belongs to ONE run: the materialization cache on
/// the region stays the shared, run-independent fact it was, and an admission (or a rejection) never
/// touches it — a restrictive run's refusal cannot poison a later permissive run, and a body admitted by
/// one run is judged afresh by the next under its own limit. Completed subtree heights and deferred
/// reach are memoized across bodies, so shared module payloads are not scanned for each materialization.
/// A rejection replays the ordinary check once to preserve its exact crossing/cycle span, independently
/// of earlier memo hits. Within a run a body is judged once per prefix, so repeated selection costs
/// one dictionary lookup. Nothing is computed for a program without deferred regions, and the
/// prefix walk over the root runs at most once, on the first
/// deferred consumption.</para>
/// </summary>
internal sealed class DeferredBodyAdmission(object root, int maxAstDepth)
{
    private const AstConsumerProfile Profile = AstConsumerProfile.EvaluatorIterativeJoinSpines;

    private readonly Lock _gate = new();
    private Dictionary<DeferredModuleRegion, int>? _prefixes;
    private Dictionary<DeferredModuleRegion, (Algorithm Body, int Prefix)>? _admitted;
    private AstStructuralPreflight.DeferredAdmissionMemo? _memo;
    private Dictionary<object, int>? _arrivals;

    /// <summary>
    /// Null when <paramref name="body"/> — the materialization of <paramref name="region"/> — is
    /// structurally safe at every position the run can consume it from; otherwise the structured
    /// rejection (<see cref="EvalError.AstDepthLimitExceeded"/> citing the run's effective limit, or
    /// <see cref="EvalError.AstCycleDetected"/>), positioned like ordinary admission: the crossing
    /// node's span or its nearest positioned ancestor within the body, otherwise the region's
    /// import site in the current document.
    /// </summary>
    internal EvalError? Admit(DeferredModuleRegion region, Algorithm body)
    {
        lock (_gate)
        {
            var memo = _memo ??= new();
            var arrivals = _arrivals ??= new(ReferenceEqualityComparer.Instance);
            if (_prefixes is null)
            {
                _prefixes = new(ReferenceEqualityComparer.Instance);
                AstStructuralPreflight.AccumulateDeferredRegionPrefixes(root, 0, Profile, _prefixes, arrivals);
            }

            if (!_prefixes.TryGetValue(region, out var prefix))
            {
                throw new InvalidOperationException(
                    "Internal error: the evaluator consumed a deferred module region that is not reachable from the " +
                    "run's admitted program or from any body the run admitted, so its structural position is unknown.");
            }

            _admitted ??= new(ReferenceEqualityComparer.Instance);
            if (_admitted.TryGetValue(region, out var admitted) && ReferenceEquals(admitted.Body, body) && admitted.Prefix >= prefix)
                return null;

            // Both consumers overwrite the materialization's root Parent: branch selection
            // wires it under the family, and output preparation takes the placeholder view's
            // parent. The placeholder's attached parent was already judged at this prefix by
            // root/body admission. A stale parent retained by RawBody is never consumed here.
            // Demand-time branch detection clears the root's parameter patterns; an output
            // view's replacement patterns were already judged on the placeholder (or, for
            // the flat-binder equivalent, as its strictly deeper family head).
            var structuralBody = body.Parent is null ? body : body switch
            {
                Algorithm.User user => user with { Parent = null },
                Algorithm.Conditional family => family with { Parent = null },
                Algorithm.Alias alias => alias with { Parent = null },
                Algorithm.Builtin => body,
            };
            if (AstStructuralPreflight.CheckDeferredBody(structuralBody, maxAstDepth - prefix, memo, out var hasDeferredRegions) is { } rejection)
            {
                return AstStructuralPreflight.ToEvalError(
                    rejection.Span is null ? rejection with { Span = region.ImportSite } : rejection,
                    maxAstDepth);
            }

            if (hasDeferredRegions)
                AstStructuralPreflight.AccumulateDeferredRegionPrefixes(structuralBody, prefix, Profile, _prefixes, arrivals, memo);
            _admitted[region] = (body, prefix);
            return null;
        }
    }
}
