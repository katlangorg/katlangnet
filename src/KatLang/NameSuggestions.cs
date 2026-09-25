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
///
/// <para>TWO PHASES (FE-1). A promotion only CAPTURES its candidate context
/// (<see cref="SuggestionContexts.Capture"/>): the exact candidate set as a
/// canonical, immutable name set derived incrementally per scope and per
/// parameter map, or the fact that the work bound was exceeded. The SELECTION —
/// comparing every candidate against the unresolved name — runs only when a
/// diagnostic renders the suggestion (<see cref="SuggestionQuery.Evaluate"/>).
/// A body nested K times under a scope that sees W names therefore costs O(1)
/// amortized per promotion instead of re-collecting, re-resolving, and
/// re-comparing the same W names K times, and a valid program that never
/// renders a suggestion never compares a candidate. The selection is a pure
/// function of the captured set — the unique closest candidate, or none — so
/// deferring it and enumerating the set in the interner's order change no
/// suggestion.</para>
/// </summary>
internal static class NameSuggestions
{
    /// <summary>Names longer than this never participate (typos in very long names are not usefully suggestable, and the bound keeps diagnostic work linear).</summary>
    internal const int MaxNameLength = 64;

    /// <summary>Above this many distinct visible candidates no suggestion is attempted (diagnostic-only work bound; realistic scopes stay far below it).</summary>
    internal const int MaxCandidates = 512;

    /// <summary>
    /// Suggests one visible name the unresolved <paramref name="name"/> is a
    /// plausible near-miss of, or <c>null</c> when no sufficiently close,
    /// unambiguous candidate exists. <paramref name="dotMemberReceiver"/> is
    /// the statically known receiver when the occurrence is a dot edge's
    /// member/fallback name and that receiver provably lacks the member;
    /// <c>null</c> for bare-name occurrences and runtime-valued receivers.
    /// Both phases at once, over a fresh context: the detector captures through
    /// its run's <see cref="SuggestionContexts"/> and evaluates on rendering.
    /// </summary>
    internal static NameSuggestion? SuggestVisibleName(
        string name,
        ElaboratedPropertyScope scope,
        ParameterOwnership parameters,
        DotMemberReceiver? dotMemberReceiver)
        => new SuggestionContexts().Capture(name, scope, parameters, dotMemberReceiver)?.Evaluate();

    /// <summary>Whether a name may be suggested for, or offered as a candidate: non-empty and within <see cref="MaxNameLength"/>.</summary>
    internal static bool IsSuggestible(string name) => name.Length is > 0 and <= MaxNameLength;

    /// <summary>
    /// The ordinary lexical policy over a captured candidate set: bound
    /// parameter names plus every name the elaborated scope can resolve, under
    /// the strict length-scaled threshold.
    /// </summary>
    internal static NameSuggestion? SelectLexicalName(
        string name,
        IEnumerable<string> candidates,
        FrontEndTraversalObservations? observations)
    {
        var maxDistance = MaxAllowedDistance(name);
        string? best = null;
        var bestDistance = int.MaxValue;
        var bestIsAmbiguous = false;
        Span<int> previousPrevious = stackalloc int[MaxNameLength + 1];
        Span<int> previous = stackalloc int[MaxNameLength + 1];
        Span<int> current = stackalloc int[MaxNameLength + 1];

        foreach (var candidateName in candidates)
        {
            observations?.RecordSuggestionCandidateExamined();
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
            : new NameSuggestion(best);
    }

    /// <summary>
    /// The member-surface policy over a receiver's captured members: the best
    /// unambiguous member typo, spelled with the receiver's qualifier, or
    /// <c>null</c>. The apparent member access is answered from that surface
    /// alone — no lexical name is offered in its place.
    /// </summary>
    internal static NameSuggestion? SelectReceiverMember(
        string name,
        IReadOnlyList<string> members,
        string? qualifier,
        FrontEndTraversalObservations? observations)
    {
        var maxDistance = MaxAllowedMemberDistance(name);
        string? best = null;
        var bestDistance = int.MaxValue;
        var bestIsAmbiguous = false;
        Span<int> previousPrevious = stackalloc int[MaxNameLength + 1];
        Span<int> previous = stackalloc int[MaxNameLength + 1];
        Span<int> current = stackalloc int[MaxNameLength + 1];

        foreach (var candidateName in members)
        {
            observations?.RecordSuggestionCandidateExamined();
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
            : new NameSuggestion(best, qualifier, isReceiverMember: true);
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

/// <summary>
/// One promotion's captured suggestion context (see <see cref="NameSuggestions"/>): the
/// unresolved name and the exact candidates it will be compared against. IMMUTABLE and
/// self-contained — it holds canonical name sets and name arrays, never a scope chain, a
/// parameter map, or a syntax tree, because a scope chain is confined to the single-threaded
/// front-end operation that built it while a suggestion is evaluated whenever, and on whichever
/// thread, a diagnostic is rendered.
/// </summary>
internal abstract class SuggestionQuery
{
    /// <summary>The suggestion; a pure function of the captured context, so every evaluation agrees.</summary>
    public abstract NameSuggestion? Evaluate();
}

/// <summary>The lexical policy over the bound and resolvable names a promotion's scope sees.</summary>
internal sealed class LexicalSuggestionQuery(
    string name,
    CanonicalNameSet candidates,
    FrontEndTraversalObservations? observations) : SuggestionQuery
{
    /// <summary>The captured candidates: every bound parameter name and every name the scope resolves.</summary>
    internal CanonicalNameSet Candidates => candidates;

    public override NameSuggestion? Evaluate()
        => NameSuggestions.SelectLexicalName(name, candidates.Names, observations);
}

/// <summary>The member policy over a statically known receiver's declared members.</summary>
internal sealed class ReceiverMemberSuggestionQuery(
    string name,
    string[] members,
    string? qualifier,
    FrontEndTraversalObservations? observations) : SuggestionQuery
{
    /// <summary>The captured candidates: the receiver's suggestible members, first occurrence each.</summary>
    internal IReadOnlyList<string> Members => members;

    public override NameSuggestion? Evaluate()
        => NameSuggestions.SelectReceiverMember(name, members, qualifier, observations);
}

/// <summary>
/// One detection run's suggestion contexts (FE-1): captures, per promotion, the exact candidate
/// set the near-miss policies will search — in O(1) amortized, however wide the scope.
///
/// <para>The lexical candidates of a promotion are its bound parameter names plus the names its
/// scope RESOLVES (<see cref="ElaboratedScopeLookup.LookupLexicalPropertyMatches"/>: a direct
/// property anywhere up the chain, or else exactly one open provider at the innermost level whose
/// providers supply the name), limited to suggestible spellings; the work bound refuses a
/// suggestion when the bound names alone, or the bound names together with every POTENTIAL
/// spelling of the scope (each level's own properties and its providers' public members), exceed
/// <see cref="NameSuggestions.MaxCandidates"/>. Every one of those sets is a canonical
/// <see cref="CanonicalNameSet"/> DERIVED incrementally, memoized per immutable input:</para>
/// <list type="bullet">
/// <item>bound names per parameter map — its parent map's plus the names that map added
/// (<see cref="ParameterOwnership.AddedNames"/>);</item>
/// <item>per scope level, from the enclosing level: potential = enclosing ∪ provided ∪ own;
/// direct = enclosing direct ∪ own; open-resolved = the names exactly one of this level's providers
/// supplies ∪ (the enclosing open-resolved names this level's providers do not supply) — a level
/// without providers keeps the enclosing open-resolved set; resolved = direct ∪ open-resolved;</item>
/// <item>provided and uniquely provided names per provider-target list, and public members per
/// target algorithm.</item>
/// </list>
/// <para>Scope levels, parameter maps, and algorithms are immutable, so each memo is a cache of a
/// pure function (reference-keyed only as a cache, never as semantic identity), and the interner's
/// memoized union/difference makes a level that adds a few names cost those names. The derivation
/// mirrors the per-name lookup exactly — owner walk first and direct-anywhere before any open,
/// then opens level by level with same-level ambiguity — and the set is only ever read through
/// <see cref="SuggestionQuery.Evaluate"/>, whose unique-closest selection is independent of
/// enumeration order.</para>
/// </summary>
internal sealed class SuggestionContexts(FrontEndTraversalObservations? observations = null)
{
    private readonly NameSetInterner _names = new(observations);
    private readonly Dictionary<ParameterOwnership, CanonicalNameSet> _boundNames = new(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<ElaboratedPropertyScope, ScopeNames> _scopeNames = new(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<Algorithm, CanonicalNameSet> _publicMembers = new(ReferenceEqualityComparer.Instance);
    private readonly Dictionary<ProviderTargets, (CanonicalNameSet Provided, CanonicalNameSet Unique)> _providedNames = [];
    private readonly Dictionary<Algorithm, string[]?> _receiverMembers = new(ReferenceEqualityComparer.Instance);

    /// <summary>
    /// The suggestion context of promoting <paramref name="name"/> in <paramref name="scope"/> under
    /// <paramref name="parameters"/>, or <c>null</c> when no suggestion is possible: the name is not
    /// suggestible, the work bound is exceeded, or there is no candidate. A statically known
    /// <paramref name="receiver"/> that declares members answers from its members alone.
    /// </summary>
    public SuggestionQuery? Capture(
        string name,
        ElaboratedPropertyScope scope,
        ParameterOwnership parameters,
        DotMemberReceiver? receiver)
    {
        if (!NameSuggestions.IsSuggestible(name))
            return null;

        if (receiver is { } member && member.Algorithm.Properties.Count > 0)
        {
            // Beyond the work bound, or with only unsuggestible declarations, the receiver still
            // declares members: the apparent member access is not answered lexically.
            return ReceiverMembers(member.Algorithm) is { Length: > 0 } members
                ? new ReceiverMemberSuggestionQuery(name, members, member.Qualifier, observations)
                : null;
        }

        var bound = BoundNames(parameters);
        if (bound.Count > NameSuggestions.MaxCandidates)
            return null;

        var visible = ScopeNamesOf(scope);
        if (_names.Union(bound, visible.Potential).Count > NameSuggestions.MaxCandidates)
            return null;

        var candidates = _names.Union(bound, visible.Resolved);
        return candidates.Count == 0 ? null : new LexicalSuggestionQuery(name, candidates, observations);
    }

    /// <summary>
    /// A receiver's suggestible members in declaration order, first occurrence each, or <c>null</c>
    /// when a suggestible declaration remains once <see cref="NameSuggestions.MaxCandidates"/>
    /// distinct members are collected (the work bound: the surface is then not searched at all).
    /// </summary>
    private string[]? ReceiverMembers(Algorithm receiver)
    {
        if (_receiverMembers.TryGetValue(receiver, out var known))
            return known;

        var seen = new HashSet<string>(StringComparer.Ordinal);
        var members = new List<string>();
        var bounded = true;
        foreach (var property in receiver.Properties)
        {
            if (!NameSuggestions.IsSuggestible(property.Name))
                continue;

            if (seen.Count >= NameSuggestions.MaxCandidates)
            {
                bounded = false;
                break;
            }

            if (seen.Add(property.Name))
                members.Add(property.Name);
        }

        known = bounded ? [.. members] : null;
        _receiverMembers.Add(receiver, known);
        return known;
    }

    private CanonicalNameSet BoundNames(ParameterOwnership parameters)
    {
        if (_boundNames.TryGetValue(parameters, out var known))
            return known;

        // The maps between this one and its nearest derived ancestor, outermost last.
        var pending = new Stack<ParameterOwnership>();
        var set = NameSetInterner.Empty;
        for (ParameterOwnership? current = parameters; current is not null; current = current.Parent)
        {
            if (_boundNames.TryGetValue(current, out set))
                break;
            pending.Push(current);
        }

        while (pending.TryPop(out var map))
        {
            set = _names.With(set, map.AddedNames.Where(NameSuggestions.IsSuggestible));
            _boundNames.Add(map, set);
        }

        return set;
    }

    private ScopeNames ScopeNamesOf(ElaboratedPropertyScope scope)
    {
        if (_scopeNames.TryGetValue(scope, out var known))
            return known;

        // The levels between this one and its nearest derived ancestor, outermost last.
        var pending = new Stack<ElaboratedPropertyScope>();
        var names = default(ScopeNames);
        for (var current = scope; current is not null; current = current.Parent)
        {
            if (_scopeNames.TryGetValue(current, out names))
                break;
            pending.Push(current);
        }

        while (pending.TryPop(out var level))
        {
            names = Derive(level, names);
            _scopeNames.Add(level, names);
        }

        return names;
    }

    private ScopeNames Derive(ElaboratedPropertyScope level, ScopeNames enclosing)
    {
        var own = _names.With(NameSetInterner.Empty, OwnNames(level));
        var providers = level.GetResolvedOpenProviders();
        if (providers.Count == 0)
        {
            return new ScopeNames(
                Potential: _names.Union(enclosing.Potential, own),
                Direct: _names.Union(enclosing.Direct, own),
                OpenResolved: enclosing.OpenResolved,
                Resolved: _names.Union(enclosing.Resolved, own));
        }

        // The innermost level whose providers supply a name decides it: resolvable only when
        // exactly one provider there supplies it; a name no provider here supplies is decided
        // farther out, exactly as it was for the enclosing level.
        var (provided, unique) = ProvidedNames(providers);
        var direct = _names.Union(enclosing.Direct, own);
        var openResolved = _names.Union(unique, _names.Except(enclosing.OpenResolved, provided));
        return new ScopeNames(
            Potential: _names.Union(_names.Union(enclosing.Potential, provided), own),
            Direct: direct,
            OpenResolved: openResolved,
            Resolved: _names.Union(direct, openResolved));
    }

    private static IEnumerable<string> OwnNames(ElaboratedPropertyScope level)
    {
        foreach (var hit in level.Properties)
        {
            if (NameSuggestions.IsSuggestible(hit.Property.Name))
                yield return hit.Property.Name;
        }
    }

    private (CanonicalNameSet Provided, CanonicalNameSet Unique) ProvidedNames(IReadOnlyList<ResolvedOpenProvider> providers)
    {
        if (providers.Count == 1)
        {
            var members = PublicMembers(providers[0].Target);
            return (members, members);
        }

        var targets = new ProviderTargets(providers);
        if (_providedNames.TryGetValue(targets, out var known))
            return known;

        // Each provider supplies each of its public names once; a name two providers supply is
        // ambiguous at this level, even when both resolved to one target.
        var provided = NameSetInterner.Empty;
        var unique = NameSetInterner.Empty;
        foreach (var provider in providers)
        {
            var members = PublicMembers(provider.Target);
            // A previous unique name survives only if absent here; a new name is unique only
            // if no earlier provider supplied it. This also keeps a third occurrence ambiguous.
            // Set algebra shares the wide provider across distinct lists with tiny local deltas.
            unique = _names.Union(_names.Except(unique, members), _names.Except(members, provided));
            provided = _names.Union(provided, members);
        }

        known = (provided, unique);
        _providedNames.Add(targets, known);
        return known;
    }

    private CanonicalNameSet PublicMembers(Algorithm target)
    {
        if (_publicMembers.TryGetValue(target, out var known))
            return known;

        known = _names.With(
            NameSetInterner.Empty,
            target.Properties.Where(static property => property.IsPublic && NameSuggestions.IsSuggestible(property.Name)).Select(static property => property.Name));
        _publicMembers.Add(target, known);
        return known;
    }

    /// <summary>A level's suggestible names: potential spellings and the resolvable ones by kind.</summary>
    private readonly record struct ScopeNames(
        CanonicalNameSet Potential,
        CanonicalNameSet Direct,
        CanonicalNameSet OpenResolved,
        CanonicalNameSet Resolved);

    /// <summary>A level's resolved provider targets, in order, compared by reference (a cache key over immutable algorithms).</summary>
    private sealed class ProviderTargets : IEquatable<ProviderTargets>
    {
        private readonly Algorithm[] _targets;
        private readonly int _hash;

        public ProviderTargets(IReadOnlyList<ResolvedOpenProvider> providers)
        {
            _targets = new Algorithm[providers.Count];
            var hash = new HashCode();
            for (var index = 0; index < providers.Count; index++)
            {
                _targets[index] = providers[index].Target;
                hash.Add(System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(_targets[index]));
            }

            _hash = hash.ToHashCode();
        }

        public bool Equals(ProviderTargets? other)
        {
            if (other is null || other._targets.Length != _targets.Length)
                return false;

            for (var index = 0; index < _targets.Length; index++)
            {
                if (!ReferenceEquals(_targets[index], other._targets[index]))
                    return false;
            }

            return true;
        }

        public override bool Equals(object? obj) => obj is ProviderTargets other && Equals(other);

        public override int GetHashCode() => _hash;
    }
}
