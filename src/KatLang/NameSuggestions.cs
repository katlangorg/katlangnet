namespace KatLang;

/// <summary>
/// The statically known receiver of a dot edge whose member/fallback name is
/// being suggested for: the receiver's algorithm (its exported structural
/// members are the member suggestion surface) and, when the receiver is
/// written as a dotted name path, the spelling a member suggestion is offered
/// after (<c>Math</c> for <c>Math.Ceil</c>; <c>null</c> keeps the bare member).
/// </summary>
internal readonly record struct DotMemberReceiver(Algorithm Algorithm, string? Qualifier);

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
/// <para>Which surface is searched follows what the written syntax most
/// plausibly targeted, never which spelling the receiver has. A dot member on
/// a statically known receiver that DECLARES members (<c>Math</c>, a block, a
/// module) is an apparent member access: the correction is searched among the
/// receiver's own members ONLY, with the member-typo policy below, and no
/// lexical name is offered in its place — <c>Math.Min</c> must not be
/// "corrected" to the unrelated collection builtin <c>min</c> merely because
/// it is a case-insensitive spelling of it; no plausible member means no
/// suggestion. A statically known receiver with NO members (a plain value
/// property, a number) makes the dotted name necessarily an extension call, so
/// the ordinary lexical policy applies exactly as for a bare name; so does a
/// runtime-valued or unresolved receiver, which may own the member.</para>
///
/// <para>The lexical match policy is deterministic and deliberately strict: a
/// case-insensitive spelling of a visible name always qualifies; otherwise the
/// optimal-string-alignment edit distance (Damerau-Levenshtein with adjacent
/// transposition) must be within a length-scaled threshold. The member-typo
/// policy searches a small, intent-implied surface, so it may look a little
/// farther (<c>Ceiling</c> → <c>Ceil</c>, <c>Dubel</c> → <c>Double</c>) but
/// guards the initial on short names (<c>Min</c> is not a misspelling of
/// <c>Sin</c>); long names may differ at the initial by just one edit.
/// Under either policy, equally close distinct
/// candidates produce NO suggestion rather than an arbitrary pick.</para>
/// </summary>
internal static class NameSuggestions
{
    /// <summary>Names longer than this never participate (typos in very long names are not usefully suggestable, and the bound keeps diagnostic work linear).</summary>
    private const int MaxNameLength = 64;

    /// <summary>Above this many distinct visible candidates no suggestion is attempted (diagnostic-only work bound; realistic scopes stay far below it).</summary>
    private const int MaxCandidates = 512;

    /// <summary>
    /// Suggests one visible name the unresolved <paramref name="name"/> is a
    /// plausible near-miss of, or <c>null</c> when no sufficiently close,
    /// unambiguous candidate exists. <paramref name="dotMemberReceiver"/> is
    /// the statically known receiver when the occurrence is a dot edge's
    /// member/fallback name and that receiver provably lacks the member;
    /// <c>null</c> for bare-name occurrences and runtime-valued receivers.
    /// </summary>
    internal static NameSuggestion? SuggestVisibleName(
        string name,
        ElaboratedPropertyScope scope,
        ParameterOwnership parameters,
        DotMemberReceiver? dotMemberReceiver)
    {
        if (name.Length == 0 || name.Length > MaxNameLength)
            return null;

        if (dotMemberReceiver is { } receiver && TrySuggestReceiverMember(name, receiver, out var memberSuggestion))
            return memberSuggestion;

        return SuggestLexicalName(name, scope, parameters);
    }

    /// <summary>
    /// The member-surface policy. Returns true when the receiver declares
    /// members reachable by structural access — the apparent member access is
    /// then answered from that surface alone, with <paramref name="suggestion"/>
    /// the best unambiguous member typo or <c>null</c> — and false for a
    /// memberless receiver, whose dotted name falls to the lexical policy.
    /// </summary>
    private static bool TrySuggestReceiverMember(
        string name,
        DotMemberReceiver receiver,
        out NameSuggestion? suggestion)
    {
        suggestion = null;
        var candidates = new Dictionary<string, Property>(StringComparer.Ordinal);

        // Structural dot access reaches any Exported property regardless of
        // publicness (the evaluator's LookupPropBinding + IsExported gate).
        foreach (var property in receiver.Algorithm.Properties)
        {
            if (property.Exposure != PropertyExposure.Exported
                || property.Name.Length == 0
                || property.Name.Length > MaxNameLength)
            {
                continue;
            }

            if (candidates.Count >= MaxCandidates)
            {
                // Beyond the work bound the surface is not searched at all: the
                // receiver still declares members, so no lexical name is offered.
                return true;
            }

            candidates.TryAdd(property.Name, property);
        }

        if (candidates.Count == 0)
            // Filtering affects the hint, not whether this is a library surface.
            // Inaccessible or over-length declarations must not revive lexical hints.
            return receiver.Algorithm.Properties.Count > 0;

        var maxDistance = MaxAllowedMemberDistance(name);
        string? best = null;
        Property? bestProperty = null;
        var bestDistance = int.MaxValue;
        var bestIsAmbiguous = false;
        Span<int> previousPrevious = stackalloc int[MaxNameLength + 1];
        Span<int> previous = stackalloc int[MaxNameLength + 1];
        Span<int> current = stackalloc int[MaxNameLength + 1];

        foreach (var (candidateName, property) in candidates)
        {
            var distance = EffectiveMemberDistance(
                name,
                candidateName,
                maxDistance,
                previousPrevious,
                previous,
                current);
            if (distance is null)
                continue;

            if (distance.Value < bestDistance)
            {
                best = candidateName;
                bestProperty = property;
                bestDistance = distance.Value;
                bestIsAmbiguous = false;
            }
            else if (distance.Value == bestDistance
                && !string.Equals(candidateName, best, StringComparison.Ordinal))
            {
                bestIsAmbiguous = true;
            }
        }

        if (!bestIsAmbiguous && best is not null)
            suggestion = new NameSuggestion(best, bestProperty, receiver.Qualifier, isReceiverMember: true);

        return true;
    }

    /// <summary>
    /// The ordinary lexical policy: bound parameter names plus every name the
    /// elaborated scope can resolve, under the strict length-scaled threshold.
    /// </summary>
    private static NameSuggestion? SuggestLexicalName(
        string name,
        ElaboratedPropertyScope scope,
        ParameterOwnership parameters)
    {
        var candidates = new Dictionary<string, Property?>(StringComparer.Ordinal);

        // Every parameter binding in scope is a safe suggestion, because the
        // owner walk always resolves such a name uniquely: the walk reaches the
        // level that binds it unless a nearer level owns a PROPERTY of that name,
        // and a direct property hit is a single declaration by construction. So
        // the corrected spelling reads either the runtime binding or that one
        // shadowing declaration — never an AmbiguousOpen, which only an unowned
        // name can be (opens are consulted after the whole owner walk). The
        // suggestion machinery deliberately does not need to distinguish the two.
        foreach (var boundName in parameters.Names)
        {
            if (!TryAddCandidate(candidates, boundName, requiredExportedProperty: null))
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
            if (!TryAddCandidate(candidates, visibleName.Name, visibleName.RequiredExportedProperty))
                return null;
        }

        if (candidates.Count == 0)
            return null;

        var maxDistance = MaxAllowedDistance(name);
        string? best = null;
        Property? bestProperty = null;
        var bestDistance = int.MaxValue;
        var bestIsAmbiguous = false;
        Span<int> previousPrevious = stackalloc int[MaxNameLength + 1];
        Span<int> previous = stackalloc int[MaxNameLength + 1];
        Span<int> current = stackalloc int[MaxNameLength + 1];

        foreach (var (candidateName, requiredExportedProperty) in candidates)
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

            if (distance.Value < bestDistance)
            {
                best = candidateName;
                bestProperty = requiredExportedProperty;
                bestDistance = distance.Value;
                bestIsAmbiguous = false;
            }
            else if (distance.Value == bestDistance
                && !string.Equals(candidateName, best, StringComparison.Ordinal))
            {
                bestIsAmbiguous = true;
            }
        }

        return bestIsAmbiguous || best is null
            ? null
            : new NameSuggestion(best, bestProperty);
    }

    private static bool TryAddCandidate(
        Dictionary<string, Property?> candidates,
        string candidate,
        Property? requiredExportedProperty)
    {
        if (candidate.Length == 0 || candidate.Length > MaxNameLength)
            return true;

        // A name that is both bound and lexically visible keeps its first
        // (ungated) registration.
        if (candidates.ContainsKey(candidate))
            return true;

        if (candidates.Count >= MaxCandidates)
            return false;

        candidates[candidate] = requiredExportedProperty;
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
    /// The member-typo threshold. A dot member on a receiver that declares
    /// members targets a small surface the writer already chose, so a
    /// misspelling may stray a little farther than a bare name may: up to half
    /// the written length, capped at three edits, once the name is long enough
    /// for that to be discriminating (<c>Ceiling</c> → <c>Ceil</c> is three
    /// edits over seven characters, <c>Dubel</c> → <c>Double</c> two over five).
    /// Short names keep the strict lexical scale.
    /// </summary>
    private static int MaxAllowedMemberDistance(string name) => name.Length switch
    {
        < 3 => 0,
        <= 4 => 1,
        _ => Math.Min(3, name.Length / 2),
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
    /// <see cref="EffectiveDistance"/> for a receiver member: the wider member
    /// threshold applies, and — beyond a pure case respelling — the candidate
    /// normally keeps the written initial letter (case-insensitively). Short
    /// names need that safeguard (<c>Min</c> must not suggest <c>Sin</c>), but
    /// a long name with just one edit may have a mistyped or transposed initial.
    /// </summary>
    private static int? EffectiveMemberDistance(
        string name,
        string candidate,
        int maxDistance,
        Span<int> previousPrevious,
        Span<int> previous,
        Span<int> current)
    {
        if (string.Equals(name, candidate, StringComparison.Ordinal))
            return null;

        if (string.Equals(name, candidate, StringComparison.OrdinalIgnoreCase))
            return 0;

        if (maxDistance == 0
            || Math.Abs(name.Length - candidate.Length) > maxDistance)
        {
            return null;
        }

        var distance = OptimalStringAlignmentDistance(
            name.ToUpperInvariant(),
            candidate.ToUpperInvariant(),
            previousPrevious,
            previous,
            current);
        var sameInitial = char.ToUpperInvariant(name[0]) == char.ToUpperInvariant(candidate[0]);
        return distance <= maxDistance
            && (sameInitial || (Math.Min(name.Length, candidate.Length) >= 5 && distance == 1))
                ? distance : null;
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
