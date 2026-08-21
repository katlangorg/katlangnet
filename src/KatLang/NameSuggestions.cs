namespace KatLang;

/// <summary>
/// Conservative near-miss suggestions for unresolved identifiers that
/// <see cref="ParameterDetector"/> promotes to implicit parameters.
/// Diagnostic-only: a suggestion never influences resolution, inference, or
/// evaluation — it is rendered beside the eventual arity/unresolved-parameter
/// diagnostic (see <see cref="ImplicitParameterProvenance"/>).
///
/// <para>Candidates come from the SAME authoritative resolution context the
/// inference used: lexical candidates are the names
/// <see cref="ElaboratedScopeLookup.LookupLexicalPropertyMatches"/> can resolve
/// (plus the already-bound capture/parameter names the detector treats as
/// bound), and dot-member candidates are the structural members ordinary dot
/// access can reach on a statically known receiver (exposure-filtered like the
/// evaluator's structural lookup; public-vs-private deliberately ignored,
/// matching structural access). No name outside those sets is ever offered.</para>
///
/// <para>The match policy is deterministic and deliberately strict: a
/// case-insensitive spelling of a visible name always qualifies; otherwise the
/// optimal-string-alignment edit distance (Damerau-Levenshtein with adjacent
/// transposition) must be within a length-scaled threshold. Equally close
/// distinct candidates produce NO suggestion rather than an arbitrary pick;
/// on a distance tie, a structural member of the receiver outranks a lexical
/// fallback candidate, mirroring structural-first dot resolution.</para>
/// </summary>
internal static class NameSuggestions
{
    /// <summary>Names longer than this never participate (typos in very long names are not usefully suggestable, and the bound keeps diagnostic work linear).</summary>
    private const int MaxNameLength = 64;

    /// <summary>Above this many distinct visible candidates no suggestion is attempted (diagnostic-only work bound; realistic scopes stay far below it).</summary>
    private const int MaxCandidates = 512;

    private const int LexicalTier = 1;
    private const int StructuralMemberTier = 0;

    /// <summary>
    /// Suggests one visible name the unresolved <paramref name="name"/> is a
    /// plausible near-miss of, or <c>null</c> when no sufficiently close,
    /// unambiguous candidate exists. <paramref name="dotMemberReceiver"/> is
    /// the statically known receiver algorithm when the occurrence is a dot
    /// edge's member/fallback name (its structural members are ranked above
    /// lexical candidates); <c>null</c> for bare-name occurrences and
    /// runtime-valued receivers.
    /// </summary>
    internal static NameSuggestion? SuggestVisibleName(
        string name,
        ElaboratedPropertyScope scope,
        IReadOnlyCollection<string> localParameterNames,
        IReadOnlyCollection<string> capturedParameterNames,
        Algorithm? dotMemberReceiver)
    {
        if (name.Length == 0 || name.Length > MaxNameLength)
            return null;

        var candidates = new Dictionary<string, Candidate>(StringComparer.Ordinal);

        if (dotMemberReceiver is not null)
        {
            // Structural dot access reaches any Exported property regardless of
            // publicness (the evaluator's LookupPropBinding + IsExported gate).
            foreach (var property in dotMemberReceiver.Properties)
            {
                if (property.Exposure == PropertyExposure.Exported)
                {
                    if (!TryAddCandidate(
                            candidates,
                            property.Name,
                            StructuralMemberTier,
                            requiredExportedProperty: property))
                    {
                        return null;
                    }
                }
            }
        }

        // A parameter owned by this algorithm always rewrites to Param. A
        // captured ancestor name rewrites only when a visible non-builtin does
        // not shadow it; with one shadowing hit the corrected spelling still
        // resolves, while multiple hits would be an AmbiguousOpen and must not
        // be suggested confidently.
        foreach (var boundName in localParameterNames)
        {
            if (!TryAddCandidate(candidates, boundName, LexicalTier, requiredExportedProperty: null))
                return null;
        }

        foreach (var boundName in capturedParameterNames)
        {
            var hits = ElaboratedScopeLookup.LookupLexicalPropertyMatches(scope, boundName);
            var hasNonBuiltinHit = hits.Any(static hit => hit.Property.Value is not Algorithm.Builtin);
            if (hasNonBuiltinHit && hits.Count > 1)
                continue;

            if (!TryAddCandidate(candidates, boundName, LexicalTier, requiredExportedProperty: null))
                return null;
        }

        var potentialNames = new HashSet<string>(candidates.Keys, StringComparer.Ordinal);
        if (!ElaboratedScopeLookup.TryCollectVisibleLexicalNames(
                scope,
                potentialNames,
                MaxCandidates,
                MaxNameLength,
                out var visibleNames))
        {
            return null;
        }

        foreach (var visibleName in visibleNames)
        {
            if (!TryAddCandidate(
                    candidates,
                    visibleName.Name,
                    LexicalTier,
                    visibleName.RequiredExportedProperty))
            {
                return null;
            }
        }

        if (candidates.Count == 0)
            return null;

        var maxDistance = MaxAllowedDistance(name);
        string? best = null;
        var bestDistance = int.MaxValue;
        var bestTier = int.MaxValue;
        var bestIsAmbiguous = false;
        Span<int> previousPrevious = stackalloc int[MaxNameLength + 1];
        Span<int> previous = stackalloc int[MaxNameLength + 1];
        Span<int> current = stackalloc int[MaxNameLength + 1];

        Candidate? bestCandidate = null;
        foreach (var (candidateName, candidate) in candidates)
        {
            var distance = EffectiveDistance(
                name,
                candidateName,
                maxDistance,
                previousPrevious,
                previous,
                current);
            if (distance is null)
                continue;

            if (distance.Value < bestDistance
                || (distance.Value == bestDistance && candidate.Tier < bestTier))
            {
                best = candidateName;
                bestCandidate = candidate;
                bestDistance = distance.Value;
                bestTier = candidate.Tier;
                bestIsAmbiguous = false;
            }
            else if (distance.Value == bestDistance
                && candidate.Tier == bestTier
                && !string.Equals(candidateName, best, StringComparison.Ordinal))
            {
                bestIsAmbiguous = true;
            }
        }

        return bestIsAmbiguous || best is null || bestCandidate is null
            ? null
            : new NameSuggestion(best, bestCandidate.Value.RequiredExportedProperty);
    }

    private readonly record struct Candidate(int Tier, Property? RequiredExportedProperty);

    private static bool TryAddCandidate(
        Dictionary<string, Candidate> candidates,
        string candidate,
        int tier,
        Property? requiredExportedProperty)
    {
        if (candidate.Length == 0 || candidate.Length > MaxNameLength)
            return true;

        // A name provided by both tiers keeps its strongest (lowest) tier.
        if (candidates.TryGetValue(candidate, out var existing))
        {
            if (tier < existing.Tier)
                candidates[candidate] = new Candidate(tier, requiredExportedProperty);
            return true;
        }

        if (candidates.Count >= MaxCandidates)
            return false;

        candidates[candidate] = new Candidate(tier, requiredExportedProperty);
        return true;
    }

    /// <summary>
    /// Length-scaled conservative threshold: very short names accept only a
    /// case-insensitive respelling, short names one edit, longer names two.
    /// </summary>
    private static int MaxAllowedDistance(string name) => name.Length switch
    {
        < 3 => 0,
        <= 5 => 1,
        _ => 2,
    };

    /// <summary>
    /// The candidate's effective distance from the unresolved name, or
    /// <c>null</c> when it does not qualify. A case-insensitive spelling of
    /// the candidate counts as distance 0 (the strongest near-miss signal,
    /// e.g. <c>Count</c> for <c>count</c>); everything else uses the exact
    /// optimal-string-alignment distance bounded by
    /// <paramref name="maxDistance"/>.
    /// </summary>
    private static int? EffectiveDistance(
        string name,
        string candidate,
        int maxDistance,
        Span<int> previousPrevious,
        Span<int> previous,
        Span<int> current)
    {
        // The identical spelling would have resolved; never "suggest" it.
        if (string.Equals(name, candidate, StringComparison.Ordinal))
            return null;

        if (string.Equals(name, candidate, StringComparison.OrdinalIgnoreCase))
            return 0;

        if (maxDistance == 0 || Math.Abs(name.Length - candidate.Length) > maxDistance)
            return null;

        var distance = OptimalStringAlignmentDistance(
            name,
            candidate,
            previousPrevious,
            previous,
            current);
        return distance <= maxDistance ? distance : null;
    }

    /// <summary>
    /// Optimal string alignment distance (Levenshtein plus adjacent
    /// transposition counted as one edit), ordinal over UTF-16 code units.
    /// Operand lengths are bounded by <see cref="MaxNameLength"/>.
    /// </summary>
    internal static int OptimalStringAlignmentDistance(string a, string b)
    {
        var previousPrevious = new int[b.Length + 1];
        var previous = new int[b.Length + 1];
        var current = new int[b.Length + 1];

        return OptimalStringAlignmentDistance(
            a,
            b,
            previousPrevious,
            previous,
            current);
    }

    private static int OptimalStringAlignmentDistance(
        string a,
        string b,
        Span<int> previousPrevious,
        Span<int> previous,
        Span<int> current)
    {
        previousPrevious = previousPrevious[..(b.Length + 1)];
        previous = previous[..(b.Length + 1)];
        current = current[..(b.Length + 1)];

        for (var j = 0; j <= b.Length; j++)
            previous[j] = j;

        for (var i = 1; i <= a.Length; i++)
        {
            current[0] = i;
            for (var j = 1; j <= b.Length; j++)
            {
                var substitutionCost = a[i - 1] == b[j - 1] ? 0 : 1;
                var value = Math.Min(
                    Math.Min(previous[j] + 1, current[j - 1] + 1),
                    previous[j - 1] + substitutionCost);

                if (i > 1 && j > 1 && a[i - 1] == b[j - 2] && a[i - 2] == b[j - 1])
                    value = Math.Min(value, previousPrevious[j - 2] + 1);

                current[j] = value;
            }

            var reusable = previousPrevious;
            previousPrevious = previous;
            previous = current;
            current = reusable;
        }

        return previous[b.Length];
    }
}
