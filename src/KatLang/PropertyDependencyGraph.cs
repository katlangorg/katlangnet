using System.Runtime.CompilerServices;

namespace KatLang;

internal readonly record struct OwnerQualifiedParameter(string Name, Algorithm? Owner)
{
    private sealed record Identity(long Value);
    private static long _nextIdentity;
    private static readonly ConditionalWeakTable<Algorithm, Identity> Identities = new();
    internal static long OwnerKey(Algorithm owner) => Identities.GetValue(owner, static _ => new(Interlocked.Increment(ref _nextIdentity))).Value;
    internal string ContentKey => $"{(Owner is null ? 0 : OwnerKey(Owner))}:{Name.Length}:{Name}";
    public bool Equals(OwnerQualifiedParameter other) => Name == other.Name && ReferenceEquals(Owner, other.Owner);
    public override int GetHashCode() => HashCode.Combine(Name, Owner is null ? 0 : RuntimeHelpers.GetHashCode(Owner));
}

/// <summary>
/// One property of the sibling-order channel: the siblings whose processed signature it READS
/// (hard edges: the topological order processes them first), and the siblings it MAY read
/// through a callee or an <c>open</c> this channel cannot classify (soft preferences: honored
/// among the properties the hard edges leave ready, so they never block the order; a cycle they
/// close is still a sibling cycle, see <see cref="PropertyDependencyGraph.CyclicIndices"/>).
/// </summary>
internal sealed record PropertyDependencyNode(
    int PropertyIndex,
    IReadOnlyList<int> SiblingDependencyIndices)
{
    public IReadOnlyList<int> SoftSiblingDependencyIndices { get; init; } = [];
}

internal sealed record PropertyDependencySummaryNode(
    int PropertyIndex,
    IReadOnlyList<int> SummarySiblingDependencyIndices,
    IReadOnlyList<string> SummaryVisiblePropertyDependencyNames,
    IReadOnlyList<string> RequiredAncestorOwnedParameterNames,
    IReadOnlyList<PendingReference> PendingReferences,
    IReadOnlyList<OwnerQualifiedParameter> OwnerQualifiedParameters);

/// <summary>
/// A reference the scope-free summary walk could not reduce to a bare visible name: a
/// static member PATH (<c>Inner.X</c> — <see cref="Head"/> <c>Inner</c>, <see cref="Members"/>
/// <c>[X]</c>), and/or a name that escaped a level owning <c>open</c> declarations, whose
/// providers are carried as <see cref="Candidates"/> (innermost level first — the order
/// <c>open</c> lookup consults them). The owning level's resolver settles it with the
/// ownership-first rule: the head as a PROPERTY of the chain first, then the candidates in
/// order, then the owning level's and its ancestors' own opens (Lean/evaluator:
/// <c>lookupLexicalProperty</c> then <c>lookupOpenPropertiesInChain</c>). Navigated members
/// charge THEIR requirement summaries — that is what makes a container that reads a captured
/// member through <c>Inner.X</c> or <c>open Inner</c> itself local-only. Immutable; equality
/// is by content so a summary fixed point can compare seeds.
/// </summary>
internal sealed class PendingReference : IEquatable<PendingReference>
{
    public PendingReference(string head, IReadOnlyList<string> members, IReadOnlyList<OpenCandidate> candidates,
        IReadOnlyList<Algorithm>? boundOwners = null, CompletedStructureContext? origin = null, bool openPath = false)
    {
        Origin = origin;
        OpenPath = openPath;
        Head = head;
        Members = members;
        Candidates = candidates;
        BoundOwners = boundOwners ?? [];
        ResolutionKey = KeyParts([origin is null ? "" : $"completed:{origin.Identity}:{openPath}", head, KeyParts(members), KeyParts(candidates.Select(static candidate => candidate.ContentKey))]);
        var boundKey = string.Join(",", BoundOwners.Select(OwnerQualifiedParameter.OwnerKey).Order());
        ContentKey = KeyParts([ResolutionKey, boundKey]);
        ShapeBoundKey = KeyParts([origin is null ? "" : $"completed:{origin.Identity}:{openPath}", head, KeyParts(members), KeyParts(candidates.Select(static candidate => candidate.ShapeKey)), boundKey]);
    }

    internal CompletedStructureContext? Origin { get; }
    internal bool OpenPath { get; }
    internal PendingReference At(CompletedStructureContext origin) => Origin is not null ? this
        : new(Head, Members, Candidates, BoundOwners, origin, OpenPath);

    public string Head { get; }

    /// <summary>Member steps navigated structurally after the head (any visibility).</summary>
    public IReadOnlyList<string> Members { get; }

    /// <summary>Open providers of the levels the reference escaped, innermost first.</summary>
    public IReadOnlyList<OpenCandidate> Candidates { get; }
    public IReadOnlyList<Algorithm> BoundOwners { get; }

    internal string ContentKey { get; }
    internal string ResolutionKey { get; }

    /// <summary>
    /// The reference without its candidates' charged seeds: head, members, candidate shapes
    /// (<see cref="OpenCandidate.ShapeKey"/>), and bound owners. References that agree on it differ
    /// only in what their resolved providers charge (see <see cref="PendingReferenceSet"/>).
    /// </summary>
    internal string ShapeBoundKey { get; }

    internal static string KeyParts(IEnumerable<string> parts)
        => string.Concat(parts.Select(static part => $"{part.Length}:{part}"));

    public PendingReference WithCandidates(IReadOnlyList<OpenCandidate> candidates)
        => new(Head, Members, candidates, BoundOwners, Origin, OpenPath);

    /// <summary>
    /// This reference with each resolved candidate's seed united with the matching candidate's seed of
    /// <paramref name="other"/> (same <see cref="ShapeBoundKey"/>). Settling a reference charges at most
    /// one candidate seed, chosen by the shape alone, and a seed's charge is the union of its entries'
    /// charges — so this reference charges exactly what the two together charge.
    /// </summary>
    internal PendingReference WithSeedsUnitedWith(PendingReference other)
    {
        var candidates = new OpenCandidate[Candidates.Count];
        for (var i = 0; i < candidates.Length; i++)
        {
            candidates[i] = Candidates[i] is ResolvedOpenCandidate resolved
                && other.Candidates[i] is ResolvedOpenCandidate otherResolved
                && resolved.ContentKey != otherResolved.ContentKey
                ? resolved.UnitedWith(otherResolved)
                : Candidates[i];
        }

        return new(Head, Members, candidates, BoundOwners, Origin, OpenPath);
    }

    public PendingReference BoundBy(Algorithm owner, bool ownerHasParameters)
        => !ownerHasParameters || BoundOwners.Any(a => ReferenceEquals(a, owner))
            ? this : new(Head, Members, Candidates, [.. BoundOwners, owner], Origin, OpenPath);

    public bool Equals(PendingReference? other) => other is not null && ContentKey == other.ContentKey;

    public override bool Equals(object? obj) => Equals(obj as PendingReference);

    public override int GetHashCode() => ContentKey.GetHashCode(StringComparison.Ordinal);
}

/// <summary>
/// Union of pending requirements, kept in a form that only GROWS as the requirements it is built
/// from grow. Repeated references with the same resolution context discharge an owner only when
/// EVERY occurrence binds it. Intersecting those bound sets implements (requirements - bound1)
/// union (requirements - bound2), without enumerating the exponentially many call paths of a
/// shared algorithm DAG.
///
/// <para>EXPOSURE-OPEN-1: references that agree on everything but their resolved candidates' charged
/// seeds (<see cref="PendingReference.ShapeBoundKey"/>) are ONE reference whose seeds are united
/// (<see cref="PendingReference.WithSeedsUnitedWith"/>, exact: settlement picks a candidate by shape
/// alone and charges a seed as the union of its entries). A candidate seed is derived from summaries
/// that grow during a fixed point, so the same written reference is produced first with a smaller
/// seed and later with a larger one. Kept apart, the two were different entries, a summary was no
/// longer monotone in the summaries it read, and around a cycle of mutually opening libraries the
/// stale entry circulated forever: the member fixed point never terminated. United, the stale seed
/// is absorbed by the larger one.</para>
/// </summary>
internal sealed class PendingReferenceSet : IReadOnlyCollection<PendingReference>
{
    private readonly Dictionary<string, PendingReference> _references = new(StringComparer.Ordinal);

    // ShapeBoundKey -> the ResolutionKey of the one reference of that shape (created on first write).
    private Dictionary<string, string>? _byShape;

    public PendingReferenceSet() { }
    public PendingReferenceSet(IEnumerable<PendingReference> references) => UnionWith(references);
    public int Count => _references.Count;
    public void Clear()
    {
        _references.Clear();
        _byShape?.Clear();
    }

    public void Add(PendingReference reference)
    {
        // Each merge removes one entry and re-adds the combined reference, so this ends after at
        // most Count merges.
        while (true)
        {
            if (_references.TryGetValue(reference.ResolutionKey, out var existing))
            {
                var common = existing.BoundOwners.Where(owner => reference.BoundOwners.Any(other => ReferenceEquals(owner, other))).ToArray();
                if (common.Length == existing.BoundOwners.Count)
                    return;
                // A narrower bound set is another shape: it may meet a reference to unite with.
                Remove(existing);
                reference = new(existing.Head, existing.Members, existing.Candidates, common, existing.Origin, existing.OpenPath);
                continue;
            }

            _byShape ??= new(StringComparer.Ordinal);
            if (_byShape.TryGetValue(reference.ShapeBoundKey, out var sameShape))
            {
                var other = _references[sameShape];
                Remove(other);
                OwnerOf(reference, other)?.RecordPendingReferenceSeedMerge();
                reference = other.WithSeedsUnitedWith(reference);
                continue;
            }

            _references.Add(reference.ResolutionKey, reference);
            _byShape.Add(reference.ShapeBoundKey, reference.ResolutionKey);
            return;
        }
    }

    private void Remove(PendingReference reference)
    {
        _references.Remove(reference.ResolutionKey);
        _byShape?.Remove(reference.ShapeBoundKey);
    }

    // The observations of the analysis the united candidates belong to.
    private static FrontEndTraversalObservations? OwnerOf(PendingReference first, PendingReference second)
        => first.Candidates.Concat(second.Candidates).OfType<ResolvedOpenCandidate>().Select(static c => c.Observations).FirstOrDefault(static o => o is not null);
    public void UnionWith(IEnumerable<PendingReference> references)
    {
        foreach (var reference in references) Add(reference);
    }
    public bool SetEquals(PendingReferenceSet other)
        => Count == other.Count && _references.All(pair => other._references.TryGetValue(pair.Key, out var value) && pair.Value.Equals(value));
    public IEnumerator<PendingReference> GetEnumerator() => _references.Values.GetEnumerator();
    System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();
}

/// <summary>
/// One <c>open</c> target of a level a <see cref="PendingReference"/> escaped. RESOLVED when
/// the level could settle it in place — the target's head was that level's own property (or an
/// inline block) and it provides the referenced name — carrying the charged requirement seed,
/// relative to the level above the one that resolved it (later levels expand it like every
/// other escaping seed). UNRESOLVED when the target's head was not a property of that level:
/// the head name and the public steps of the dotted target are carried outward for a level
/// whose direct chain declares the head. A target that provides nothing is not a candidate.
/// A C# <c>closed</c> class: the two sealed classes below are its only kinds. Its consumers
/// are switch STATEMENTS (no compiler exhaustiveness); the <c>default</c> arm of
/// <c>PropertyDependencyGraphBuilder.AddEscaping</c> is a semantic default — an unresolved
/// candidate whose head this level does not declare is carried outward unchanged — not an
/// unknown-kind guard.
/// </summary>
internal closed class OpenCandidate
{
    private protected OpenCandidate(int providerLevel) => ProviderLevel = providerLevel;

    /// <summary>
    /// The opener level this candidate's <c>open</c> target is declared at, numbered along the
    /// reference's escape path (innermost first, ascending). The candidates of ONE level are
    /// ONE open lookup — the evaluator's <c>LookupOpens</c> (Lean <c>lookupOpenProperties</c>)
    /// collects every provider of the first level that provides the name and reports two as
    /// <c>ambiguousOpen</c> — so settlement compares them together and never lets list order
    /// pick between them. Carried unchanged when a candidate is re-seeded or settled outward.
    /// </summary>
    internal int ProviderLevel { get; }

    internal abstract string ContentKey { get; }

    /// <summary>
    /// The candidate WITHOUT its charged seed: kind, opener level, and provider (or carried target).
    /// Two references whose candidates agree on it are settled by the same providers in the same
    /// order, so their resolved seeds may be united (<see cref="PendingReferenceSet"/>).
    /// </summary>
    internal abstract string ShapeKey { get; }
}

/// <summary>
/// EXPOSURE-OPEN-1: a resolved candidate is an IMMUTABLE analysis node. Its seed can hold further
/// resolved candidates — a chain of N members read through <c>open</c> and settled at one owner
/// nests N deep — so every candidate is shared by reference wherever it is carried, and a
/// transformation that cannot change it returns it unchanged. Two cached facts make that decision
/// exact without walking the nesting: the candidate's DEEP FACTS (<see cref="Facts"/>: every pending
/// head, required name, and owner-qualified input anywhere inside it, as one canonical set of the
/// summary memo) and its content key, which names its seed by the memo's exact interned id
/// (<see cref="PropertyDependencyGraphBuilder.SummaryMemo.SeedKeyId"/>) instead of re-serializing the
/// nesting. Both are memo-relative, like <see cref="IdentityKey"/>: a candidate never meets another
/// memo's candidates.
/// </summary>
internal sealed class ResolvedOpenCandidate : OpenCandidate
{
    private readonly PropertyDependencyGraphBuilder.SummaryMemo _memo;
    private string? _contentKey;

    public ResolvedOpenCandidate(
        PropertyDependencyGraphBuilder.SummarySeed seed,
        int providerLevel,
        OpenProviderIdentity identity,
        PropertyDependencyGraphBuilder.SummaryMemo memo)
        : this(seed, providerLevel, identity, memo.ProviderIdentityKey(identity), memo, facts: null)
    {
    }

    private ResolvedOpenCandidate(
        PropertyDependencyGraphBuilder.SummarySeed seed,
        int providerLevel,
        OpenProviderIdentity identity,
        int identityKey,
        PropertyDependencyGraphBuilder.SummaryMemo memo,
        SeedFacts? facts)
        : base(providerLevel)
    {
        Seed = seed;
        Identity = identity;
        IdentityKey = identityKey;
        _memo = memo;
        // Built from the seed's own entries and the facts its nested candidates already carry: no
        // walk of the nesting, and no recursion.
        Facts = facts ?? seed.DeepFacts(memo.SeedFacts);
    }

    /// <summary>Frozen: never mutated after construction; readers clone before accumulating.</summary>
    public PropertyDependencyGraphBuilder.SummarySeed Seed { get; }

    /// <summary>
    /// The SEMANTIC identity of the provider this candidate settled (Q-19 D-I): two candidates
    /// of one open lookup with equal identities are one provider, charged once. Built within the
    /// body that settled it and extended as the reference escapes (see
    /// <see cref="OpenProviderIdentity.IsComplete"/>).
    /// </summary>
    public OpenProviderIdentity Identity { get; }

    /// <summary>The summary analysis's key for <see cref="Identity"/> (part of the content key).</summary>
    public int IdentityKey { get; }

    /// <summary>Every pending head, required name, and owner-qualified input in the seed, nested candidates included.</summary>
    internal SeedFacts Facts { get; }

    /// <summary>The observations of the analysis that built this candidate.</summary>
    internal FrontEndTraversalObservations? Observations => _memo.Observations;

    /// <summary>The same candidate — same opener level and provider — carrying a re-derived seed.</summary>
    public ResolvedOpenCandidate WithSeed(PropertyDependencyGraphBuilder.SummarySeed seed)
    {
        _memo.Observations?.RecordOpenCandidateSeedRebuild();
        return new(seed, ProviderLevel, Identity, IdentityKey, _memo, facts: null);
    }

    /// <summary>The same candidate after its reference escaped the body <paramref name="level"/>.</summary>
    public ResolvedOpenCandidate EscapedThrough(Algorithm level)
    {
        var identity = Identity.EscapedThrough(level);
        return ReferenceEquals(identity, Identity)
            ? this
            : new(Seed, ProviderLevel, identity, _memo.ProviderIdentityKey(identity), _memo, Facts) { _contentSeedKey = _contentSeedKey };
    }

    /// <summary>
    /// <see cref="PropertyDependencyGraphBuilder.SummarySeed.UnderMissingLexicalHead(string)"/> of the seed: this
    /// candidate itself when nothing inside it is a pending reference to <paramref name="head"/>, so
    /// the reduction never rebuilds a nesting it cannot change.
    /// </summary>
    public ResolvedOpenCandidate UnderMissingLexicalHead(string head)
        => CandidateRewriteFrame.Run(UnderMissingLexicalHead(head, new(StringComparer.Ordinal), out var unchanged)) ?? unchanged;

    /// <summary>
    /// The rewrite's own test and memo for this reach of the candidate: null with
    /// <paramref name="result"/> when nothing is rebuilt, otherwise the frame that rebuilds it
    /// (its <see cref="CandidateRewriteFrame.Candidate"/> is the result).
    /// </summary>
    internal CandidateRewriteFrame? UnderMissingLexicalHead(string head, Dictionary<string, ResolvedOpenCandidate> transformed,
        out ResolvedOpenCandidate result)
    {
        result = this;
        if (!_memo.SeedFacts.HasHead(Facts, head))
            return null;
        if (transformed.TryGetValue(ContentKey, out var memoized))
        {
            result = memoized;
            return null;
        }
        var frame = new CandidateRewriteFrame();
        frame.Body = RebuildUnderMissingLexicalHead(frame, head, transformed);
        return frame;
    }

    private IEnumerator<CandidateRewriteFrame> RebuildUnderMissingLexicalHead(CandidateRewriteFrame self, string head,
        Dictionary<string, ResolvedOpenCandidate> transformed)
    {
        var seed = new CandidateRewriteFrame();
        seed.Body = Seed.UnderMissingLexicalHead(seed, head, transformed);
        yield return seed;
        transformed.Add(ContentKey, self.Candidate = WithSeed(seed.Seed!));
    }

    // Each transformation dictionary belongs to ONE operation with fixed head/owner/name-set
    // inputs. Exact candidate keys share both equal nodes and repeated reaches of one node. It is
    // discarded on return: no mutable name-set context or summary-map version needs retaining.

    /// <summary>
    /// The seed with every requirement <paramref name="owner"/> binds owner-qualified
    /// (<see cref="PropertyDependencyGraphBuilder.SummarySeed.QualifyParameters(Algorithm, IReadOnlySet{string}, FrontEndTraversalObservations)"/>): this candidate
    /// itself when nothing inside it requires one of <paramref name="ownerParameterNames"/>.
    /// </summary>
    public ResolvedOpenCandidate QualifiedBy(Algorithm owner, IReadOnlySet<string> ownerParameterNames)
        => CandidateRewriteFrame.Run(QualifiedBy(owner, ownerParameterNames, new(StringComparer.Ordinal), out var unchanged)) ?? unchanged;

    /// <summary>The frame form of <see cref="QualifiedBy(Algorithm, IReadOnlySet{string})"/> (see <see cref="UnderMissingLexicalHead(string, Dictionary{string, ResolvedOpenCandidate}, out ResolvedOpenCandidate)"/>).</summary>
    internal CandidateRewriteFrame? QualifiedBy(Algorithm owner, IReadOnlySet<string> ownerParameterNames,
        Dictionary<string, ResolvedOpenCandidate> transformed, out ResolvedOpenCandidate result)
    {
        result = this;
        if (!_memo.SeedFacts.RequiresAnyName(Facts, ownerParameterNames, owner: null))
            return null;
        if (transformed.TryGetValue(ContentKey, out var memoized))
        {
            result = memoized;
            return null;
        }
        var frame = new CandidateRewriteFrame();
        frame.Body = RebuildQualifiedBy(frame, owner, ownerParameterNames, transformed);
        return frame;
    }

    private IEnumerator<CandidateRewriteFrame> RebuildQualifiedBy(CandidateRewriteFrame self, Algorithm owner,
        IReadOnlySet<string> ownerParameterNames, Dictionary<string, ResolvedOpenCandidate> transformed)
    {
        var seed = Seed.Clone();
        if (seed.QualifyParameters(owner, ownerParameterNames, _memo.Observations, transformed) is { } nested)
            yield return new CandidateRewriteFrame { Body = nested };
        transformed.Add(ContentKey, self.Candidate = WithSeed(seed));
    }

    /// <summary>The frame form of the requirement strip of the seed (see <see cref="UnderMissingLexicalHead(string, Dictionary{string, ResolvedOpenCandidate}, out ResolvedOpenCandidate)"/>).</summary>
    internal CandidateRewriteFrame? WithoutRequiredParameters(IReadOnlySet<string> names, Algorithm owner, bool ownerHasParameters,
        Dictionary<string, ResolvedOpenCandidate> transformed, out ResolvedOpenCandidate result)
    {
        result = this;
        if (!RequiresAny(names, owner))
            return null;
        if (transformed.TryGetValue(ContentKey, out var memoized))
        {
            result = memoized;
            return null;
        }
        var frame = new CandidateRewriteFrame();
        frame.Body = RebuildWithoutRequiredParameters(frame, names, owner, ownerHasParameters, transformed);
        return frame;
    }

    private IEnumerator<CandidateRewriteFrame> RebuildWithoutRequiredParameters(CandidateRewriteFrame self, IReadOnlySet<string> names,
        Algorithm owner, bool ownerHasParameters, Dictionary<string, ResolvedOpenCandidate> transformed)
    {
        var seed = Seed.Clone();
        if (seed.RemoveRequiredAncestorOwnedParameterNames(names, owner, ownerHasParameters, _memo.Observations, transformed) is { } nested)
            yield return new CandidateRewriteFrame { Body = nested };
        transformed.Add(ContentKey, self.Candidate = WithSeed(seed));
    }

    /// <summary>Whether anything inside the seed requires one of <paramref name="names"/>, unqualified or owned by <paramref name="owner"/>.</summary>
    public bool RequiresAny(IReadOnlySet<string> names, Algorithm owner)
        => _memo.SeedFacts.RequiresAnyName(Facts, names, owner);

    /// <summary>The same candidate whose seed is this seed united with <paramref name="other"/>'s (one provider, so one charge).</summary>
    public ResolvedOpenCandidate UnitedWith(ResolvedOpenCandidate other)
    {
        // Exact immutable inputs: no mutable member-map context or partial cycle result is retained.
        var left = ContentKey;
        var right = other.ContentKey;
        var key = string.CompareOrdinal(left, right) <= 0 ? (left, right) : (right, left);
        var united = _memo.UnitedCandidates ??= new();
        if (!united.TryGetValue(key, out var result))
            united.Add(key, result = WithSeed(Seed.Clone().Absorb(other.Seed)));
        return result;
    }

    // The interned id of the seed's content, kept by a re-identified copy of the same seed.
    private int? _contentSeedKey;

    internal override string ContentKey
    {
        get
        {
            if (_contentKey is null)
            {
                _contentSeedKey ??= _memo.SeedKeyId(Seed.ContentKeyFor(_memo.Observations));
                _contentKey = $"resolved@{ProviderLevel}#{IdentityKey}({_contentSeedKey})";
                _memo.Observations?.RecordOpenCandidateKeyCharacters(_contentKey.Length);
            }

            return _contentKey;
        }
    }

    internal override string ShapeKey => $"resolved@{ProviderLevel}#{IdentityKey}";
}

/// <summary>
/// OOS-22: ONE suspended step of a rewrite of a resolved candidate's nesting — a seed's own rewrite
/// (<see cref="PropertyDependencyGraphBuilder.SummarySeed.QualifyParameters(Algorithm, IReadOnlySet{string}, FrontEndTraversalObservations)"/>,
/// <see cref="PropertyDependencyGraphBuilder.SummarySeed.RemoveRequiredAncestorOwnedParameterNames(IReadOnlySet{string}, Algorithm, bool, FrontEndTraversalObservations)"/>,
/// <see cref="PropertyDependencyGraphBuilder.SummarySeed.UnderMissingLexicalHead(string)"/>) or one nested
/// candidate's rebuild. A candidate's seed holds the candidates it settled through, so an opened
/// chain nests candidates as deep as it is long, and these rewrites reach every changed level of
/// that nesting: they never recurse on the host stack. A body yields the frame of a nested
/// candidate it must rebuild and resumes with its <see cref="Candidate"/>; the order of every
/// deep-fact test, memo lookup and rebuild is the recursive form's. A rewrite has no active state of
/// its own (its memo admits a candidate only after its rebuild completes), so an exception simply
/// abandons the operation's memo.
/// </summary>
internal sealed class CandidateRewriteFrame
{
    public IEnumerator<CandidateRewriteFrame> Body = null!;
    public ResolvedOpenCandidate? Candidate;
    public PropertyDependencyGraphBuilder.SummarySeed? Seed;

    /// <summary>Runs <paramref name="root"/> (if any) to completion; its <see cref="Candidate"/>, or null without a frame.</summary>
    internal static ResolvedOpenCandidate? Run(CandidateRewriteFrame? root)
    {
        if (root is null)
            return null;
        Run(root.Body);
        return root.Candidate;
    }

    /// <summary>Runs one rewrite body to completion over an explicit stack (no stack when it rebuilds nothing).</summary>
    internal static void Run(IEnumerator<CandidateRewriteFrame> body)
    {
        if (!body.MoveNext())
            return;

        var frames = new Stack<IEnumerator<CandidateRewriteFrame>>();
        frames.Push(body);
        frames.Push(body.Current.Body);
        try
        {
            while (frames.TryPeek(out var frame))
            {
                if (frame.MoveNext())
                    frames.Push(frame.Current.Body);
                else
                    frames.Pop();
            }
        }
        finally
        {
            while (frames.TryPop(out var suspended))
                suspended.Dispose();
        }
    }
}

internal sealed class UnresolvedOpenCandidate(string head, IReadOnlyList<string> publicSteps, int providerLevel) : OpenCandidate(providerLevel)
{
    public string Head { get; } = head;

    public IReadOnlyList<string> PublicSteps { get; } = publicSteps;

    internal override string ContentKey => $"open@{ProviderLevel}" + PendingReference.KeyParts([Head, PendingReference.KeyParts(PublicSteps)]);

    internal override string ShapeKey => ContentKey;
}

/// <summary>
/// One deep fact of a resolved open candidate's seed (<see cref="ResolvedOpenCandidate.Facts"/>): a
/// pending reference's head, a required ancestor-owned name, or an owner-qualified input — each with
/// the exact identity its kind compares by (names ordinally, owners by reference).
/// </summary>
internal readonly record struct SeedFact(SeedFactKind Kind, OwnerQualifiedParameter Parameter);

internal enum SeedFactKind
{
    PendingHead,
    Required,
    Qualified,
}

/// <summary>A canonical set of <see cref="SeedFact"/>s: one hash-consed node per distinct content.</summary>
internal readonly struct SeedFacts(CanonicalSetInterner<SeedFact>.Node? root)
{
    internal CanonicalSetInterner<SeedFact>.Node? Root { get; } = root;

    public int Count => Root?.Count ?? 0;
}

/// <summary>
/// The summary memo's run-local interner of deep candidate facts — the third instance of the one
/// canonical-set engine (<see cref="CanonicalSetInterner{TElement}"/>). A candidate's facts are its
/// seed's own entries united with its nested candidates' facts: shared structure, built once per
/// candidate, so testing what a nesting contains costs a lookup, never a walk.
/// </summary>
internal sealed class SeedFactInterner(FrontEndTraversalObservations? observations)
    : CanonicalSetInterner<SeedFact>(EqualityComparer<SeedFact>.Default)
{
    public SeedFacts With(SeedFacts set, IEnumerable<SeedFact> facts) => new(WithElements(set.Root, facts));

    public SeedFacts Union(SeedFacts first, SeedFacts second) => new(UnionRoots(first.Root, second.Root));

    public bool HasHead(SeedFacts facts, string head)
    {
        observations?.RecordOpenCandidateFactProbe();
        return facts.Count > 0 && ContainsElement(facts.Root, new(SeedFactKind.PendingHead, new(head, null)));
    }

    /// <summary>
    /// Whether <paramref name="facts"/> require one of <paramref name="names"/> — unqualified, or (when
    /// <paramref name="owner"/> is given) qualified by that owner — scanning the SMALLER side.
    /// </summary>
    public bool RequiresAnyName(SeedFacts facts, IReadOnlySet<string> names, Algorithm? owner)
    {
        if (facts.Count == 0 || names.Count == 0)
            return false;

        if (facts.Count <= names.Count)
        {
            foreach (var fact in EnumerateElements(facts.Root))
            {
                observations?.RecordOpenCandidateFactProbe();
                if (fact.Kind == SeedFactKind.Required && names.Contains(fact.Parameter.Name))
                    return true;
                if (owner is not null && fact.Kind == SeedFactKind.Qualified
                    && ReferenceEquals(fact.Parameter.Owner, owner) && names.Contains(fact.Parameter.Name))
                    return true;
            }

            return false;
        }

        foreach (var name in names)
        {
            observations?.RecordOpenCandidateFactProbe();
            if (ContainsElement(facts.Root, new(SeedFactKind.Required, new(name, null))))
                return true;
            if (owner is not null && ContainsElement(facts.Root, new(SeedFactKind.Qualified, new(name, owner))))
                return true;
        }

        return false;
    }
}

/// <summary>
/// Sibling/processing-order channel result: per-property direct sibling dependency edges and
/// the topological property-processing order derived from them (<see cref="TopologicalOrder"/>:
/// a sibling CYCLE is ordered as one unit, so its declaration-order fallback never reaches a
/// property outside it). This is the ONLY channel the implicit-argument resolver consumes; the
/// recursive summary channel lives on <see cref="PropertyDependencySummaryGraph"/> and is never
/// computed here (M17).
/// </summary>
internal sealed class PropertyDependencyGraph
{
    public static PropertyDependencyGraph Empty { get; } = new(
        Array.Empty<Property>(),
        new Dictionary<string, int>(StringComparer.Ordinal),
        Array.Empty<PropertyDependencyNode>());

    private readonly Dictionary<string, int> propertyNameToIndex;
    private readonly PropertyDependencyNode[] nodes;
    private IReadOnlyList<int>? topologicalOrder;

    public PropertyDependencyGraph(
        IReadOnlyList<Property> properties,
        Dictionary<string, int> propertyNameToIndex,
        PropertyDependencyNode[] nodes)
    {
        Properties = properties;
        this.propertyNameToIndex = propertyNameToIndex;
        this.nodes = nodes;
    }

    public IReadOnlyList<Property> Properties { get; }

    public int Count => nodes.Length;

    public PropertyDependencyNode this[int propertyIndex] => nodes[propertyIndex];

    public bool TryGetPropertyIndex(string propertyName, out int propertyIndex)
        => propertyNameToIndex.TryGetValue(propertyName, out propertyIndex);

    /// <summary>
    /// The order the resolver processes the level's properties in: Kahn's order over the
    /// CONDENSATION of the hard edges, followed by settlement of any cycles soft preferences close
    /// around those units (<see cref="SettleSoftCycleConsumers"/>). A property outside every sibling cycle is ready once every
    /// sibling it reads is processed; a sibling CYCLE — a strongly connected component of more than
    /// one property — is ONE unit, ready once every sibling its members read OUTSIDE it is processed,
    /// and is released only when no property outside a cycle is ready. Releasing a cycle processes
    /// its members together in declaration order: its processing-order fallback, in which a member
    /// processed first reads the others unprocessed. That fallback is confined to the cycle's
    /// members (X-04): a property that depends on a cycle is not part of it, so it waits for all of
    /// the cycle's members and reads their settled signatures, whatever the declaration order. Soft
    /// preferences decide among ready units as among ready properties (see
    /// <see cref="PropertyDependencyNode"/>); ties go to declaration order. If a soft preference closes
    /// a cycle, only its members retain that fallback; consumers outside the combined component
    /// follow all its members. Settlement preserves the hard scheduler's internal component order.
    /// </summary>
    public IReadOnlyList<int> TopologicalOrder
        => topologicalOrder ??= BuildTopologicalOrder();

    /// <summary>
    /// The properties the resolver never processes ahead of their turn on demand: every member of a
    /// sibling CYCLE — closed by the reads this channel classifies (hard edges) or by the ones it
    /// only anticipates (soft preferences) alike — and everything that hard-depends on one. A cycle
    /// keeps its processing-order fallback (a member processed first reads the others unprocessed),
    /// whichever reads close it: processing a member early would only move which member reads
    /// another one unprocessed, and around a long ring it would stack one processing inside the
    /// next. A property that hard-depends on a cycle is not part of that fallback — its turn comes
    /// after all of the cycle's members (<see cref="TopologicalOrder"/>) — but processing it early
    /// would process the cycle early, so it waits for its turn too. Computed on first use, so a
    /// level without demands never pays for it.
    /// </summary>
    public IReadOnlySet<int> CyclicIndices => cyclicIndices ??= BuildCyclicIndices();

    private HashSet<int>? cyclicIndices;

    private HashSet<int> BuildCyclicIndices()
    {
        // The members of every strongly connected component of more than one property over hard
        // AND soft edges (the channel records no edge from a property to itself).
        var count = nodes.Length;
        var component = StronglyConnectedComponents(includeSoft: true, out var componentCount);
        var componentSize = new int[componentCount];
        foreach (var unit in component)
            componentSize[unit]++;

        var cyclic = new HashSet<int>();
        for (var property = 0; property < count; property++)
        {
            if (componentSize[component[property]] > 1)
                cyclic.Add(property);
        }

        // Everything that hard-depends on a cycle member.
        var dependents = new List<int>?[count];
        foreach (var node in nodes)
        {
            foreach (var dependency in node.SiblingDependencyIndices)
                (dependents[dependency] ??= []).Add(node.PropertyIndex);
        }

        var pending = new Queue<int>(cyclic);
        while (pending.TryDequeue(out var property))
        {
            if (dependents[property] is not { } waiting)
                continue;
            foreach (var dependent in waiting)
            {
                if (cyclic.Add(dependent))
                    pending.Enqueue(dependent);
            }
        }

        return cyclic;
    }

    private IReadOnlyList<int> BuildTopologicalOrder()
    {
        var count = nodes.Length;
        // Most levels are leaves: no property, or one (the channel records no edge to itself).
        if (count <= 1)
            return count == 0 ? [] : [0];

        // The UNITS of the order: the strongly connected components of the hard edges. A component
        // of one property is that property; a larger one is a sibling CYCLE, whose members — in
        // declaration order, the cycle's processing-order fallback — are processed together.
        var component = StronglyConnectedComponents(includeSoft: false, out var componentCount);
        var members = new List<int>[componentCount];
        for (var unit = 0; unit < componentCount; unit++)
            members[unit] = [];
        for (var property = 0; property < count; property++)
            members[component[property]].Add(property);

        // A unit is keyed by its first member (a property outside every cycle by itself).
        int UnitOf(int property) => members[component[property]][0];
        bool InCycle(int property) => members[component[property]].Count > 1;

        // What a unit still waits for OUTSIDE itself, per property outside every cycle and per cycle
        // (keyed by its first member): the unprocessed siblings it reads (hard edges), and the
        // unprocessed siblings it may read (soft preferences). A read inside a cycle never blocks it.
        var pending = new int[count];
        var softPending = new int[count];
        var dependents = new List<int>?[count];
        var softDependents = new List<int>?[count];
        foreach (var node in nodes)
        {
            var unit = UnitOf(node.PropertyIndex);
            foreach (var dependencyIndex in node.SiblingDependencyIndices)
            {
                if (component[dependencyIndex] == component[node.PropertyIndex])
                    continue;
                (dependents[dependencyIndex] ??= []).Add(node.PropertyIndex);
                pending[unit]++;
            }

            // SOFT preferences (reads this channel cannot classify): among the units the hard edges
            // leave ready, one whose soft dependencies are all processed goes first, in readiness
            // order; only when none is, the earliest ready one does (a soft edge never blocks the
            // order, so it can never create a cycle). A level without soft edges or cycles orders
            // exactly as plain Kahn does.
            foreach (var softIndex in node.SoftSiblingDependencyIndices)
            {
                if (component[softIndex] == component[node.PropertyIndex])
                    continue;
                (softDependents[softIndex] ??= []).Add(node.PropertyIndex);
                softPending[unit]++;
            }
        }

        var queue = new Queue<int>();
        var blocked = new SortedSet<(long Sequence, int Index)>();
        var blockedSequence = new long[count];
        var nextSequence = 0L;
        // Ready cycles by first member, i.e. by declaration: those whose soft preferences outside the
        // cycle are all processed, and those still waiting for one.
        var readyCycles = new SortedSet<int>();
        var softBlockedCycles = new SortedSet<int>();

        void MakeReady(int unit)
        {
            if (InCycle(unit))
            {
                (softPending[unit] == 0 ? readyCycles : softBlockedCycles).Add(unit);
                return;
            }

            if (softPending[unit] == 0)
            {
                queue.Enqueue(unit);
                return;
            }

            blockedSequence[unit] = nextSequence++;
            blocked.Add((blockedSequence[unit], unit));
        }

        for (var property = 0; property < count; property++)
        {
            if (pending[property] == 0 && UnitOf(property) == property)
                MakeReady(property);
        }

        var result = new List<int>(count);
        void Process(int propertyIndex)
        {
            result.Add(propertyIndex);
            if (dependents[propertyIndex] is { } waiting)
            {
                foreach (var dependentIndex in waiting)
                {
                    var unit = UnitOf(dependentIndex);
                    if (--pending[unit] == 0)
                        MakeReady(unit);
                }
            }

            if (softDependents[propertyIndex] is { } preferring)
            {
                foreach (var dependentIndex in preferring)
                {
                    var unit = UnitOf(dependentIndex);
                    if (--softPending[unit] != 0)
                        continue;
                    if (InCycle(unit))
                    {
                        if (softBlockedCycles.Remove(unit))
                            readyCycles.Add(unit);
                    }
                    else if (blocked.Remove((blockedSequence[unit], unit)))
                    {
                        queue.Enqueue(unit);
                    }
                }
            }
        }

        while (true)
        {
            if (queue.TryDequeue(out var ready))
            {
                Process(ready);
                continue;
            }

            // A cycle is released only when no property outside one is ready (a property that does
            // not depend on a cycle keeps its place ahead of it): first a cycle whose soft preferences
            // are satisfied, then a property waiting only on a soft preference, then any ready cycle.
            int cycle;
            if (readyCycles.Count > 0)
            {
                cycle = readyCycles.Min;
                readyCycles.Remove(cycle);
            }
            else if (blocked.Count > 0)
            {
                var next = blocked.Min;
                blocked.Remove(next);
                Process(next.Index);
                continue;
            }
            else if (softBlockedCycles.Count > 0)
            {
                cycle = softBlockedCycles.Min;
                softBlockedCycles.Remove(cycle);
            }
            else
            {
                break;
            }

            foreach (var member in members[component[cycle]])
                Process(member);
        }

        // The condensation is acyclic, so every unit becomes ready: a property left out means the
        // bookkeeping above is wrong, never that the program is.
        if (result.Count != count)
        {
            throw new InvalidOperationException(
                $"Internal error: the sibling processing order placed {result.Count} of {count} properties.");
        }

        return SettleSoftCycleConsumers(result, componentCount);
    }

    /// <summary>
    /// A soft preference may close a cycle around one or more hard units. The hard-unit scheduler
    /// must break that preference inside the cycle, but its stall fallback must not reach an
    /// acyclic consumer outside it. Order the combined-edge condensation using the hard scheduler's
    /// order as the tie-breaker AND as each component's internal order. This preserves every
    /// within-cycle choice (Q-76), including hard dependency order inside a mixed cycle, while every
    /// outside consumer waits for the whole provider component to settle. No fixed-point rewriting.
    /// </summary>
    private IReadOnlyList<int> SettleSoftCycleConsumers(List<int> hardOrder, int hardComponentCount)
    {
        if (!nodes.Any(static node => node.SoftSiblingDependencyIndices.Count > 0))
            return hardOrder;

        var component = StronglyConnectedComponents(includeSoft: true, out var componentCount);
        // Adding soft edges can only merge hard components. With no merge, the hard scheduler
        // already honors every external preference: the component preference graph is acyclic.
        if (componentCount == hardComponentCount)
            return hardOrder;

        var members = new List<int>[componentCount];
        var priority = new int[componentCount];
        Array.Fill(priority, int.MaxValue);
        for (var unit = 0; unit < componentCount; unit++)
            members[unit] = [];
        for (var position = 0; position < hardOrder.Count; position++)
        {
            var property = hardOrder[position];
            var unit = component[property];
            priority[unit] = Math.Min(priority[unit], position);
            members[unit].Add(property);
        }

        var pending = new int[componentCount];
        var dependents = new List<int>?[componentCount];
        void AddRead(int reader, int provider)
        {
            var from = component[reader];
            var to = component[provider];
            if (from == to)
                return;
            pending[from]++;
            (dependents[to] ??= []).Add(from);
        }
        foreach (var node in nodes)
        {
            foreach (var dependency in node.SiblingDependencyIndices)
                AddRead(node.PropertyIndex, dependency);
            foreach (var dependency in node.SoftSiblingDependencyIndices)
                AddRead(node.PropertyIndex, dependency);
        }

        var ready = new PriorityQueue<int, int>();
        for (var unit = 0; unit < componentCount; unit++)
            if (pending[unit] == 0)
                ready.Enqueue(unit, priority[unit]);
        var settled = new List<int>(nodes.Length);
        while (ready.TryDequeue(out var unit, out _))
        {
            settled.AddRange(members[unit]);
            if (dependents[unit] is not { } waiting)
                continue;
            foreach (var dependent in waiting)
                if (--pending[dependent] == 0)
                    ready.Enqueue(dependent, priority[dependent]);
        }
        if (settled.Count != nodes.Length)
            throw new InvalidOperationException("Internal error: the combined sibling condensation was not acyclic.");
        return settled;
    }

    /// <summary>
    /// Tarjan's strongly connected components of the level's properties over the hard edges and,
    /// with <paramref name="includeSoft"/>, the soft preferences too — ITERATIVELY, so a long chain
    /// or ring of siblings never grows the host stack. Returns each property's component number;
    /// only membership matters (the numbering is Tarjan's completion order).
    /// </summary>
    private int[] StronglyConnectedComponents(bool includeSoft, out int componentCount)
    {
        var count = nodes.Length;
        var order = new int[count];
        var low = new int[count];
        var onStack = new bool[count];
        var component = new int[count];
        Array.Fill(order, -1);
        var components = new Stack<int>();
        var work = new Stack<(int Property, int Edge)>();
        var nextOrder = 0;
        var completed = 0;

        void Enter(int property)
        {
            order[property] = low[property] = nextOrder++;
            components.Push(property);
            onStack[property] = true;
            work.Push((property, 0));
        }

        for (var start = 0; start < count; start++)
        {
            if (order[start] >= 0)
                continue;

            Enter(start);
            while (work.TryPop(out var frame))
            {
                var hard = nodes[frame.Property].SiblingDependencyIndices;
                IReadOnlyList<int> soft = includeSoft ? nodes[frame.Property].SoftSiblingDependencyIndices : [];
                if (frame.Edge < hard.Count + soft.Count)
                {
                    work.Push((frame.Property, frame.Edge + 1));
                    var dependency = frame.Edge < hard.Count ? hard[frame.Edge] : soft[frame.Edge - hard.Count];
                    if (order[dependency] < 0)
                        Enter(dependency);
                    else if (onStack[dependency])
                        low[frame.Property] = Math.Min(low[frame.Property], order[dependency]);
                    continue;
                }

                if (work.TryPeek(out var parent))
                    low[parent.Property] = Math.Min(low[parent.Property], low[frame.Property]);
                if (low[frame.Property] != order[frame.Property])
                    continue;

                int member;
                do
                {
                    member = components.Pop();
                    onStack[member] = false;
                    component[member] = completed;
                }
                while (member != frame.Property);
                completed++;
            }
        }

        componentCount = completed;
        return component;
    }
}

/// <summary>
/// Recursive summary channel result: per-property recursive ancestor-capture facts — direct
/// required ancestor-owned parameter names plus summary edges to visible names and sibling
/// properties. This is the ONLY channel the exposure resolver consumes; the sibling/order
/// channel lives on <see cref="PropertyDependencyGraph"/> and is never computed here (M17).
/// </summary>
internal sealed class PropertyDependencySummaryGraph
{
    private readonly Dictionary<string, int> propertyNameToIndex;
    private readonly PropertyDependencySummaryNode[] nodes;

    public PropertyDependencySummaryGraph(
        IReadOnlyList<Property> properties,
        Dictionary<string, int> propertyNameToIndex,
        PropertyDependencySummaryNode[] nodes)
    {
        Properties = properties;
        this.propertyNameToIndex = propertyNameToIndex;
        this.nodes = nodes;
    }

    public IReadOnlyList<Property> Properties { get; }

    public int Count => nodes.Length;

    public PropertyDependencySummaryNode this[int propertyIndex] => nodes[propertyIndex];

    public bool TryGetPropertyIndex(string propertyName, out int propertyIndex)
        => propertyNameToIndex.TryGetValue(propertyName, out propertyIndex);
}

/// <summary>
/// FE-4a: the order in which a level's fixed-point equations are FIRST evaluated — every equation
/// after the equations it statically reads (the postorder of a depth-first walk over those read edges,
/// cycles broken where the walk closes them). It is an evaluation order only: any fair iteration of
/// the level's monotone equations reaches the same least fixed point, but a dependency-first order lets
/// one pass carry a chain or a cycle whole instead of advancing one step per round, however the
/// properties are declared. The walk is iterative (a long chain costs no host stack).
/// </summary>
internal static class DependencyFirstOrder
{
    /// <param name="count">The number of equations.</param>
    /// <param name="isEquation">Whether an index is an equation to order (a name's representative).</param>
    /// <param name="reads">The equation indices an equation statically reads.</param>
    public static List<int> Of(int count, Func<int, bool> isEquation, Func<int, IEnumerable<int>> reads)
    {
        var order = new List<int>(count);
        var visited = new bool[count];
        var stack = new Stack<(int Index, IEnumerator<int> Reads)>();
        for (var root = 0; root < count; root++)
        {
            if (visited[root] || !isEquation(root))
                continue;

            visited[root] = true;
            stack.Push((root, reads(root).GetEnumerator()));
            while (stack.TryPeek(out var frame))
            {
                if (frame.Reads.MoveNext())
                {
                    var next = frame.Reads.Current;
                    if (!visited[next] && isEquation(next))
                    {
                        visited[next] = true;
                        stack.Push((next, reads(next).GetEnumerator()));
                    }

                    continue;
                }

                frame.Reads.Dispose();
                stack.Pop();
                order.Add(frame.Index);
            }
        }

        return order;
    }

    /// <summary>
    /// The strongly connected components of the equations over the static read edges, dependency
    /// first (Tarjan's order: a component is emitted after every component it reads). Iterative.
    /// </summary>
    public static List<List<int>> Components(int count, Func<int, bool> isEquation, Func<int, IEnumerable<int>> reads)
    {
        var components = new List<List<int>>();
        var index = new int[count];
        var lowLink = new int[count];
        var onStack = new bool[count];
        Array.Fill(index, -1);
        var nextIndex = 0;
        var stack = new Stack<int>();
        var frames = new Stack<(int Node, IEnumerator<int> Reads)>();
        for (var root = 0; root < count; root++)
        {
            if (index[root] >= 0 || !isEquation(root))
                continue;

            Enter(root);
            while (frames.TryPeek(out var frame))
            {
                if (frame.Reads.MoveNext())
                {
                    var next = frame.Reads.Current;
                    if (!isEquation(next))
                        continue;
                    if (index[next] < 0)
                        Enter(next);
                    else if (onStack[next])
                        lowLink[frame.Node] = Math.Min(lowLink[frame.Node], index[next]);
                    continue;
                }

                frame.Reads.Dispose();
                frames.Pop();
                if (frames.TryPeek(out var caller))
                    lowLink[caller.Node] = Math.Min(lowLink[caller.Node], lowLink[frame.Node]);
                if (lowLink[frame.Node] != index[frame.Node])
                    continue;

                var component = new List<int>();
                int member;
                do
                {
                    member = stack.Pop();
                    onStack[member] = false;
                    component.Add(member);
                }
                while (member != frame.Node);
                component.Reverse();
                components.Add(component);
            }
        }

        return components;

        void Enter(int node)
        {
            index[node] = lowLink[node] = nextIndex++;
            stack.Push(node);
            onStack[node] = true;
            frames.Push((node, reads(node).GetEnumerator()));
        }
    }
}

internal static class PropertyDependencyGraphBuilder
{
    /// <summary>
    /// Mutable name-set accumulator AND value of the summary channel. Callers mutate returned
    /// seeds in place (<see cref="UnionWith"/>) while accumulating an enclosing expression's
    /// contribution, so a completed summary admitted to a memo is stored as a PRISTINE CLONE
    /// and every reach — first or later — receives its own mutable copy; returning a stored
    /// instance directly would let one reader's accumulation corrupt every later reader. For
    /// the same reason there is deliberately NO shared <c>Empty</c> singleton: every empty
    /// seed is a fresh mutable instance.
    ///
    /// <para>SHARED ARGUMENT BUNDLES (FE-2): implicit lifting gives every lifted reference to one
    /// callable in a region the SAME synthesized argument bundle, so K call edges contribute one
    /// bundle's seed — L names. A call edge therefore takes a large completed bundle seed BY
    /// REFERENCE (<see cref="AbsorbCompleted"/>) instead of copying its names, clones and unions
    /// carry such references along, and the seed folds every distinct absorbed seed in exactly
    /// once — transitively, in absorption order — the first time any of its sets is read. The
    /// content of every set is the union it always was; only when the copying happens moved.
    /// A small completed seed is still copied (at most <see cref="CopiedCompletedEntries"/>
    /// entries per edge), so written calls keep their exact eager behavior.</para>
    /// </summary>
    internal sealed class SummarySeed
    {
        /// <summary>
        /// The largest completed seed an edge copies rather than references: copying it costs a
        /// constant per edge, and it keeps small written argument bundles out of the absorbed
        /// lists (a long operator chain of distinct small calls would otherwise carry one
        /// reference per call at every node of the chain).
        /// </summary>
        internal const int CopiedCompletedEntries = 8;

        // The four sets are created on first WRITE (SEC-S1): most seeds — a literal's, a resolved
        // name's, every completed seed's pristine clone — stay empty, and four eagerly allocated
        // empty collections per seed were the exposure pass's largest live cost on dense source.
        // Null means empty: every internal read treats it so, and each public accessor
        // materializes the real, mutable set callers may change in place, once.
        private HashSet<string>? _requiredAncestorOwnedParameterNames;
        private HashSet<string>? _visiblePropertyDependencyNames;
        private PendingReferenceSet? _pendingReferences;
        private HashSet<OwnerQualifiedParameter>? _ownerQualifiedParameters;

        // Completed seeds absorbed by reference, in absorption order, deduplicated by reference;
        // null once folded (or when nothing was absorbed). An absorbed seed is never mutated.
        private List<SummarySeed>? _absorbed;
        private HashSet<SummarySeed>? _absorbedSet;

        public SummarySeed(
            IEnumerable<string>? requiredAncestorOwnedParameterNames = null,
            IEnumerable<string>? visiblePropertyDependencyNames = null,
            IEnumerable<PendingReference>? pendingReferences = null,
            IEnumerable<OwnerQualifiedParameter>? ownerQualifiedParameters = null)
        {
            _requiredAncestorOwnedParameterNames = IsKnownEmpty(requiredAncestorOwnedParameterNames) ? null : NonEmptyOrNull(CreateNameSet(requiredAncestorOwnedParameterNames));
            _visiblePropertyDependencyNames = IsKnownEmpty(visiblePropertyDependencyNames) ? null : NonEmptyOrNull(CreateNameSet(visiblePropertyDependencyNames));
            _pendingReferences = IsKnownEmpty(pendingReferences) ? null : new PendingReferenceSet(pendingReferences!) is { Count: > 0 } references ? references : null;
            _ownerQualifiedParameters = IsKnownEmpty(ownerQualifiedParameters) ? null : NonEmptyOrNull(new HashSet<OwnerQualifiedParameter>(ownerQualifiedParameters!));
        }

        private static bool IsKnownEmpty<T>(IEnumerable<T>? items)
            => items is null || (items is IReadOnlyCollection<T> collection && collection.Count == 0);

        private static HashSet<T>? NonEmptyOrNull<T>(HashSet<T> set) => set.Count == 0 ? null : set;

        public HashSet<string> RequiredAncestorOwnedParameterNames
        {
            get { Fold(); return _requiredAncestorOwnedParameterNames ??= CreateNameSet(); }
        }

        public HashSet<OwnerQualifiedParameter> OwnerQualifiedParameters
        {
            get { Fold(); return _ownerQualifiedParameters ??= []; }
        }

        /// <summary>Bare names no level between the reference and the consumer resolved, with no open providers on the way.</summary>
        public HashSet<string> VisiblePropertyDependencyNames
        {
            get { Fold(); return _visiblePropertyDependencyNames ??= CreateNameSet(); }
        }

        /// <summary>Member paths and open-shadowed names (see <see cref="PendingReference"/>).</summary>
        public PendingReferenceSet PendingReferences
        {
            get { Fold(); return _pendingReferences ??= new(); }
        }

        // Entries a copy of this seed would transfer, without folding it.
        private int EntryCount
            => (_requiredAncestorOwnedParameterNames?.Count ?? 0) + (_visiblePropertyDependencyNames?.Count ?? 0)
                + (_pendingReferences?.Count ?? 0) + (_ownerQualifiedParameters?.Count ?? 0) + (_absorbed?.Count ?? 0);

        public SummarySeed Clone()
        {
            var clone = new SummarySeed(
                _requiredAncestorOwnedParameterNames, _visiblePropertyDependencyNames, _pendingReferences, _ownerQualifiedParameters);
            clone.AbsorbAll(_absorbed);
            return clone;
        }

        public void UnionWith(SummarySeed other)
        {
            UnionOwnSets(other);
            AbsorbAll(other._absorbed);
        }

        // Adds another seed's OWN sets (not its absorbed parts) to this seed's, creating a set
        // only when the other one contributes an entry.
        private void UnionOwnSets(SummarySeed other)
        {
            if (other._requiredAncestorOwnedParameterNames is { Count: > 0 } required)
                (_requiredAncestorOwnedParameterNames ??= CreateNameSet()).UnionWith(required);
            if (other._visiblePropertyDependencyNames is { Count: > 0 } visible)
                (_visiblePropertyDependencyNames ??= CreateNameSet()).UnionWith(visible);
            if (other._pendingReferences is { Count: > 0 } pending)
                (_pendingReferences ??= new()).UnionWith(pending);
            if (other._ownerQualifiedParameters is { Count: > 0 } qualified)
                (_ownerQualifiedParameters ??= []).UnionWith(qualified);
        }

        /// <summary><see cref="UnionWith"/> returning this seed, for expression-shaped folds.</summary>
        public SummarySeed Absorb(SummarySeed other)
        {
            UnionWith(other);
            return this;
        }

        /// <summary>
        /// A carried open candidate is used only after lexical lookup of its head has failed.
        /// Under that same assumption, a nested lookup of the SAME head with a fully resolved
        /// first provider level can already select its sole provider (or select nothing on
        /// ambiguity). Keeping it symbolic repeatedly wraps a cycle's previous summary in
        /// another identical condition and never reaches a finite fixed point.
        /// </summary>
        internal SummarySeed UnderMissingLexicalHead(string head)
        {
            var frame = new CandidateRewriteFrame();
            frame.Body = UnderMissingLexicalHead(frame, head, new(StringComparer.Ordinal));
            CandidateRewriteFrame.Run(frame.Body);
            return frame.Seed!;
        }

        /// <summary>The frame body of <see cref="UnderMissingLexicalHead(string)"/>; its result is <paramref name="self"/>'s seed.</summary>
        internal IEnumerator<CandidateRewriteFrame> UnderMissingLexicalHead(CandidateRewriteFrame self, string head,
            Dictionary<string, ResolvedOpenCandidate> transformed)
        {
            var result = new SummarySeed(RequiredAncestorOwnedParameterNames,
                VisiblePropertyDependencyNames, ownerQualifiedParameters: OwnerQualifiedParameters);
            foreach (var pending in PendingReferences)
            {
                // A nested candidate that holds no reference to the head is returned as it is
                // (EXPOSURE-OPEN-1), so this never rebuilds a nesting it cannot change.
                var candidates = new OpenCandidate[pending.Candidates.Count];
                for (var i = 0; i < candidates.Length; i++)
                {
                    candidates[i] = pending.Candidates[i];
                    if (candidates[i] is not ResolvedOpenCandidate resolved)
                        continue;
                    if (resolved.UnderMissingLexicalHead(head, transformed, out var rewritten) is { } rebuild)
                    {
                        yield return rebuild;
                        rewritten = rebuild.Candidate!;
                    }

                    candidates[i] = rewritten;
                }
                var firstLevel = candidates.TakeWhile(c => c.ProviderLevel == candidates[0].ProviderLevel).ToArray();
                if (pending.Head == head && firstLevel.Length > 0 && firstLevel.All(c => c is ResolvedOpenCandidate))
                {
                    // Q-19 D-I: the level's PROVIDERS decide — candidates of one provider are one.
                    if (firstLevel.Select(c => ((ResolvedOpenCandidate)c).Identity).Distinct().Count() == 1)
                    {
                        var selected = ((ResolvedOpenCandidate)firstLevel[0]).Seed.Clone();
                        selected.OwnerQualifiedParameters.RemoveWhere(r => r.Owner is not null
                            && pending.BoundOwners.Any(owner => ReferenceEquals(owner, r.Owner)));
                        var nested = selected.PendingReferences.ToArray();
                        selected.PendingReferences.Clear();
                        foreach (var reference in nested)
                        {
                            var bound = reference;
                            foreach (var owner in pending.BoundOwners)
                                bound = bound.BoundBy(owner, ownerHasParameters: true);
                            selected.PendingReferences.Add(bound);
                        }
                        result.UnionWith(selected);
                    }
                    continue;
                }
                result.PendingReferences.Add(SameCandidates(pending.Candidates, candidates) ? pending : pending.WithCandidates(candidates));
            }
            self.Seed = result;
        }

        private static bool SameCandidates(IReadOnlyList<OpenCandidate> before, IReadOnlyList<OpenCandidate> after)
        {
            for (var i = 0; i < before.Count; i++)
            {
                if (!ReferenceEquals(before[i], after[i]))
                    return false;
            }

            return true;
        }

        /// <summary>
        /// EXPOSURE-OPEN-1: the deep facts of a seed a resolved open candidate is built over — its own
        /// required names, owner-qualified inputs, and pending heads, united with the facts its nested
        /// candidates already carry (so building them never walks the nesting).
        /// </summary>
        internal SeedFacts DeepFacts(SeedFactInterner interner)
        {
            Fold();
            var facts = default(SeedFacts);
            if (_requiredAncestorOwnedParameterNames is { Count: > 0 } required)
                facts = interner.With(facts, required.Select(static name => new SeedFact(SeedFactKind.Required, new(name, null))));
            if (_ownerQualifiedParameters is { Count: > 0 } qualified)
                facts = interner.With(facts, qualified.Select(static parameter => new SeedFact(SeedFactKind.Qualified, parameter)));
            if (_pendingReferences is not { Count: > 0 } pendingReferences)
                return facts;

            facts = interner.With(facts, pendingReferences.Select(static pending => new SeedFact(SeedFactKind.PendingHead, new(pending.Head, null))));
            foreach (var pending in pendingReferences)
            {
                foreach (var candidate in pending.Candidates)
                {
                    if (candidate is ResolvedOpenCandidate resolved)
                        facts = interner.Union(facts, resolved.Facts);
                }
            }

            return facts;
        }

        /// <summary>
        /// Adds a COMPLETED seed — one a memo stores and nothing mutates afterwards: a large one
        /// by reference (a shared argument bundle's seed, FE-2), a small one by copying.
        /// </summary>
        public SummarySeed AbsorbCompleted(SummarySeed completed)
        {
            if (completed.EntryCount <= CopiedCompletedEntries)
                UnionWith(completed);
            else
                AbsorbReference(completed);
            return this;
        }

        private void AbsorbAll(List<SummarySeed>? parts)
        {
            if (parts is null)
                return;
            foreach (var part in parts)
                AbsorbReference(part);
        }

        // A short absorbed list deduplicates by scanning it; the reference set exists only once
        // the list outgrows this (SEC-S1: K seeds each absorbing ONE shared bundle seed kept K
        // one-element hash sets alive). Membership is the same reference-identity test either way.
        private const int AbsorbedScanLimit = 8;

        private void AbsorbReference(SummarySeed part)
        {
            if (_absorbedSet is { } set)
            {
                if (set.Add(part))
                    _absorbed!.Add(part);
                return;
            }

            var absorbed = _absorbed ??= [];
            if (AbsorbedListContains(absorbed, part))
                return;
            absorbed.Add(part);
            if (absorbed.Count > AbsorbedScanLimit)
                _absorbedSet = new(absorbed, ReferenceEqualityComparer.Instance);
        }

        private bool HasAbsorbed(SummarySeed part)
            => _absorbedSet?.Contains(part) ?? (_absorbed is { } absorbed && AbsorbedListContains(absorbed, part));

        private static bool AbsorbedListContains(List<SummarySeed> absorbed, SummarySeed part)
        {
            foreach (var existing in absorbed)
            {
                if (ReferenceEquals(existing, part))
                    return true;
            }

            return false;
        }

        /// <summary>
        /// FE-3: removes, WITHOUT folding it, every absorbed completed part whose whole content is
        /// required ancestor-owned names that <paramref name="owned"/> covers. Called only where
        /// the caller next qualifies and strips exactly the owned names at the owning level (an
        /// algorithm summary's output seed), where such a part contributes nothing to the result —
        /// so the result is the one folding would produce, while K owners that each absorbed one
        /// shared L-name argument-bundle seed no longer each copy, qualify, and strip its L names.
        /// The verdict per (part, owned set) is memoized on <paramref name="memo"/>.
        /// </summary>
        internal void DropOwnedAbsorbedParts(IReadOnlySet<string> owned, SummaryMemo memo)
        {
            if (_absorbed is not { } absorbed || owned.Count == 0)
                return;

            List<SummarySeed>? kept = null;
            for (var i = 0; i < absorbed.Count; i++)
            {
                var part = absorbed[i];
                if (memo.IsOwnedPureRequirement(part, owned))
                {
                    kept ??= absorbed.GetRange(0, i);
                    continue;
                }

                kept?.Add(part);
            }

            if (kept is null)
                return;
            _absorbed = kept.Count == 0 ? null : kept;
            _absorbedSet = kept.Count > AbsorbedScanLimit ? new HashSet<SummarySeed>(kept, ReferenceEqualityComparer.Instance) : null;
        }

        /// <summary>
        /// Whether this COMPLETED seed and every part it absorbed carry only required names, all in
        /// <paramref name="owned"/>. Reads the stored sets directly: a completed seed is never folded
        /// or mutated.
        /// </summary>
        internal bool IsPureRequirementWithin(IReadOnlySet<string> owned, FrontEndTraversalObservations? observations = null)
            => RequiredNamesOutside(owned, observations: observations) is { Length: 0 };

        /// <summary>
        /// When this COMPLETED seed and every part it absorbed carry only required names: those names
        /// that <paramref name="covered"/> does not contain (distinct, in walk order); otherwise null.
        /// Reads the stored sets directly: a completed seed is never folded or mutated.
        /// </summary>
        internal string[]? RequiredNamesOutside(IReadOnlySet<string> covered,
            Func<SummarySeed, IReadOnlySet<string>, string[]?>? residualOf = null,
            FrontEndTraversalObservations? observations = null)
        {
            List<string>? outside = null;
            HashSet<string>? seenOutside = null;
            var visited = new HashSet<SummarySeed>(ReferenceEqualityComparer.Instance);
            var pending = new Stack<SummarySeed>();
            pending.Push(this);
            while (pending.TryPop(out var part))
            {
                if (!visited.Add(part))
                    continue;
                if (part._visiblePropertyDependencyNames is { Count: > 0 }
                    || part._pendingReferences is { Count: > 0 }
                    || part._ownerQualifiedParameters is { Count: > 0 })
                {
                    return null;
                }

                foreach (var name in part._requiredAncestorOwnedParameterNames ?? [])
                {
                    observations?.RecordSummaryResidualNameProbe();
                    if (!covered.Contains(name) && (seenOutside ??= new(StringComparer.Ordinal)).Add(name))
                        (outside ??= []).Add(name);
                }

                if (part._absorbed is { } nested)
                {
                    foreach (var absorbedPart in nested)
                    {
                        if (residualOf is null)
                            pending.Push(absorbedPart);
                        else
                        {
                            var residual = residualOf(absorbedPart, covered);
                            if (residual is null)
                                return null;
                            foreach (var name in residual)
                                if ((seenOutside ??= new(StringComparer.Ordinal)).Add(name))
                                    (outside ??= []).Add(name);
                        }
                    }
                }
            }

            return outside is null ? [] : [.. outside];
        }

        // Folds every distinct absorbed seed into this seed's own sets — each once, depth-first in
        // absorption order, so the resulting content and insertion order are deterministic.
        private void Fold()
        {
            if (_absorbed is not { } absorbed)
                return;

            _absorbed = null;
            _absorbedSet = null;
            var folded = new HashSet<SummarySeed>(ReferenceEqualityComparer.Instance);
            var pending = new Stack<SummarySeed>();
            for (var i = absorbed.Count - 1; i >= 0; i--)
                pending.Push(absorbed[i]);
            while (pending.TryPop(out var part))
            {
                if (!folded.Add(part))
                    continue;

                UnionOwnSets(part);
                if (part._absorbed is { } nested)
                {
                    for (var i = nested.Count - 1; i >= 0; i--)
                        pending.Push(nested[i]);
                }
            }
        }

        /// <summary>
        /// Moves every requirement <paramref name="owner"/> binds into an owner-qualified one —
        /// in this seed and in the resolved open candidates riding along. Only the intersection
        /// with the owner's parameter names matters, so the SMALLER side is scanned (FE-1): a
        /// narrow seed under a wide owner costs its own size, never the owner's width, and
        /// <paramref name="ownerParameterNames"/> is the owner's set built once per resolution
        /// (<see cref="SummaryMemo.ParameterNamesOf"/>), never a live projection per property.
        /// </summary>
        public void QualifyParameters(
            Algorithm owner,
            IReadOnlySet<string> ownerParameterNames,
            FrontEndTraversalObservations? observations)
        {
            if (QualifyParameters(owner, ownerParameterNames, observations, new(StringComparer.Ordinal)) is { } candidates)
                CandidateRewriteFrame.Run(candidates);
        }

        /// <summary>
        /// The frame form of <see cref="QualifyParameters(Algorithm, IReadOnlySet{string}, FrontEndTraversalObservations)"/>:
        /// qualifies this seed's own requirements now and returns the body that rewrites its carried
        /// candidates (null when it carries no pending reference), for <see cref="CandidateRewriteFrame"/>.
        /// </summary>
        internal IEnumerator<CandidateRewriteFrame>? QualifyParameters(Algorithm owner, IReadOnlySet<string> ownerParameterNames,
            FrontEndTraversalObservations? observations, Dictionary<string, ResolvedOpenCandidate> transformed)
        {
            // Reads the folded sets directly, so a seed with nothing to qualify materializes none.
            Fold();
            if (_requiredAncestorOwnedParameterNames is { Count: > 0 } required)
            {
                foreach (var name in SharedNames(required, ownerParameterNames, observations))
                {
                    required.Remove(name);
                    (_ownerQualifiedParameters ??= []).Add(new(name, owner));
                }
            }

            return _pendingReferences is { Count: > 0 } pendingReferences
                ? QualifyCandidates(pendingReferences, owner, ownerParameterNames, transformed)
                : null;
        }

        private static IEnumerator<CandidateRewriteFrame> QualifyCandidates(PendingReferenceSet pendingReferences, Algorithm owner,
            IReadOnlySet<string> ownerParameterNames, Dictionary<string, ResolvedOpenCandidate> transformed)
        {
            // Only references whose carried candidates require one of the owner's names change; a
            // candidate that requires none is kept as it is (EXPOSURE-OPEN-1: its deep facts decide).
            List<PendingReference>? rewritten = null;
            var changed = false;
            foreach (var reference in pendingReferences)
            {
                var candidates = new OpenCandidate[reference.Candidates.Count];
                for (var i = 0; i < candidates.Length; i++)
                {
                    candidates[i] = reference.Candidates[i];
                    if (candidates[i] is not ResolvedOpenCandidate resolved)
                        continue;
                    if (resolved.QualifiedBy(owner, ownerParameterNames, transformed, out var qualified) is { } rebuild)
                    {
                        yield return rebuild;
                        qualified = rebuild.Candidate!;
                    }

                    candidates[i] = qualified;
                }

                var same = SameCandidates(reference.Candidates, candidates);
                changed |= !same;
                (rewritten ??= new(pendingReferences.Count)).Add(same ? reference : reference.WithCandidates(candidates));
            }

            if (!changed)
                yield break;
            pendingReferences.Clear();
            pendingReferences.UnionWith(rewritten!);
        }

        /// <summary>
        /// Strips the names a level itself binds from every requirement the seed carries —
        /// its own and those of the resolved open candidates riding along, which are seeds
        /// relative to the same level. <paramref name="ownerHasParameters"/> is whether
        /// <paramref name="owner"/> declares any parameter, decided once by the caller. Every
        /// intersection scans its smaller side (FE-1).
        /// </summary>
        public void RemoveRequiredAncestorOwnedParameterNames(
            IReadOnlySet<string> names,
            Algorithm owner,
            bool ownerHasParameters,
            FrontEndTraversalObservations? observations)
        {
            if (RemoveRequiredAncestorOwnedParameterNames(names, owner, ownerHasParameters, observations, new(StringComparer.Ordinal)) is { } candidates)
                CandidateRewriteFrame.Run(candidates);
        }

        /// <summary>
        /// The frame form of <see cref="RemoveRequiredAncestorOwnedParameterNames(IReadOnlySet{string}, Algorithm, bool, FrontEndTraversalObservations)"/>:
        /// strips this seed's own requirements now and returns the body that rewrites its pending
        /// references (null when it carries none), for <see cref="CandidateRewriteFrame"/>.
        /// </summary>
        internal IEnumerator<CandidateRewriteFrame>? RemoveRequiredAncestorOwnedParameterNames(IReadOnlySet<string> names, Algorithm owner,
            bool ownerHasParameters, FrontEndTraversalObservations? observations, Dictionary<string, ResolvedOpenCandidate> transformed)
        {
            // Reads the folded sets directly, so a seed with nothing to strip materializes none.
            Fold();
            if (_requiredAncestorOwnedParameterNames is { Count: > 0 } required)
            {
                foreach (var name in SharedNames(required, names, observations))
                    required.Remove(name);
            }

            _ownerQualifiedParameters?.RemoveWhere(r => ReferenceEquals(r.Owner, owner) && names.Contains(r.Name));
            return _pendingReferences is { Count: > 0 } pendingReferences
                ? StripCandidates(pendingReferences, names, owner, ownerHasParameters, transformed)
                : null;
        }

        private static IEnumerator<CandidateRewriteFrame> StripCandidates(PendingReferenceSet pendingReferences, IReadOnlySet<string> names,
            Algorithm owner, bool ownerHasParameters, Dictionary<string, ResolvedOpenCandidate> transformed)
        {
            var rewritten = new List<PendingReference>(pendingReferences.Count);
            var changed = ownerHasParameters;
            foreach (var pending in pendingReferences)
            {
                if (pending.Candidates.Count == 0)
                {
                    rewritten.Add(pending.BoundBy(owner, ownerHasParameters));
                    continue;
                }

                var candidates = new List<OpenCandidate>(pending.Candidates.Count);
                foreach (var candidate in pending.Candidates)
                {
                    var stripped = candidate;
                    if (candidate is ResolvedOpenCandidate resolved)
                    {
                        if (resolved.WithoutRequiredParameters(names, owner, ownerHasParameters, transformed, out var kept) is { } rebuild)
                        {
                            yield return rebuild;
                            kept = rebuild.Candidate!;
                        }

                        stripped = kept;
                    }

                    candidates.Add(stripped);
                    changed |= !ReferenceEquals(stripped, candidate);
                }

                rewritten.Add((SameCandidates(pending.Candidates, candidates) ? pending : pending.WithCandidates(candidates)).BoundBy(owner, ownerHasParameters));
            }

            if (!changed)
                yield break;

            pendingReferences.Clear();
            pendingReferences.UnionWith(rewritten);
        }

        // The names in both sets, found by scanning the SMALLER one (each examined name is one
        // qualification probe): the one intersection every requirement strip and qualification uses.
        private static List<string> SharedNames(
            HashSet<string> requirements,
            IReadOnlySet<string> names,
            FrontEndTraversalObservations? observations)
        {
            var shared = new List<string>();
            if (requirements.Count == 0 || names.Count == 0)
                return shared;

            if (requirements.Count <= names.Count)
            {
                foreach (var name in requirements)
                {
                    observations?.RecordSummaryQualificationProbe();
                    if (names.Contains(name))
                        shared.Add(name);
                }
            }
            else
            {
                foreach (var name in names)
                {
                    observations?.RecordSummaryQualificationProbe();
                    if (requirements.Contains(name))
                        shared.Add(name);
                }
            }

            return shared;
        }

        public bool SetEquals(SummarySeed other)
            => RequiredAncestorOwnedParameterNames.SetEquals(other.RequiredAncestorOwnedParameterNames)
                && VisiblePropertyDependencyNames.SetEquals(other.VisiblePropertyDependencyNames)
                && PendingReferences.SetEquals(other.PendingReferences)
                && OwnerQualifiedParameters.SetEquals(other.OwnerQualifiedParameters);

        /// <summary>
        /// FE-4a: whether the seed's content is empty, decided WITHOUT folding: its own sets and every
        /// seed it holds by reference (transitively) are empty. Reads only; a seed held by reference is
        /// never mutated, and the parts form no cycle (a seed only ever holds seeds built before it).
        /// </summary>
        internal bool IsEmptyWithoutFolding()
        {
            if (!OwnSetsEmpty(this))
                return false;
            if (_absorbed is null)
                return true;

            var visited = new HashSet<SummarySeed>(ReferenceEqualityComparer.Instance) { this };
            var pending = new Stack<SummarySeed>(_absorbed);
            while (pending.TryPop(out var part))
            {
                if (!visited.Add(part))
                    continue;
                if (!OwnSetsEmpty(part))
                    return false;
                if (part._absorbed is { } nested)
                {
                    foreach (var nestedPart in nested)
                        pending.Push(nestedPart);
                }
            }

            return true;

            static bool OwnSetsEmpty(SummarySeed seed)
                => (seed._requiredAncestorOwnedParameterNames?.Count ?? 0) == 0
                    && (seed._visiblePropertyDependencyNames?.Count ?? 0) == 0
                    && (seed._pendingReferences?.Count ?? 0) == 0
                    && (seed._ownerQualifiedParameters?.Count ?? 0) == 0;
        }

        /// <summary>
        /// FE-4a: a SUFFICIENT test of equal content that never folds: equal own sets and the same
        /// seeds held by reference. False means "not decided here" (compare <see cref="SetEquals"/>).
        /// </summary>
        internal bool StructurallyEquals(SummarySeed other)
        {
            // The absorbed lists are deduplicated by reference, so equal counts plus containment
            // is set equality.
            if ((_absorbed?.Count ?? 0) != (other._absorbed?.Count ?? 0))
                return false;
            if (_absorbed is { } parts)
            {
                foreach (var part in parts)
                {
                    if (!other.HasAbsorbed(part))
                        return false;
                }
            }

            return SameNames(_requiredAncestorOwnedParameterNames, other._requiredAncestorOwnedParameterNames)
                && SameNames(_visiblePropertyDependencyNames, other._visiblePropertyDependencyNames)
                && ((_pendingReferences?.Count ?? 0) == 0
                    ? (other._pendingReferences?.Count ?? 0) == 0
                    : other._pendingReferences is { } otherPending && _pendingReferences!.SetEquals(otherPending))
                && SameNames(_ownerQualifiedParameters, other._ownerQualifiedParameters);

            // Set equality with a missing set read as the empty set.
            static bool SameNames<T>(HashSet<T>? left, HashSet<T>? right)
                => (left?.Count ?? 0) == 0
                    ? (right?.Count ?? 0) == 0
                    : right is not null && left!.SetEquals(right);
        }

        public bool IsEmpty
        {
            get
            {
                Fold();
                return (_requiredAncestorOwnedParameterNames?.Count ?? 0) == 0
                    && (_visiblePropertyDependencyNames?.Count ?? 0) == 0
                    && (_pendingReferences?.Count ?? 0) == 0
                    && (_ownerQualifiedParameters?.Count ?? 0) == 0;
            }
        }

        /// <summary>Content identity (sorted), for candidate equality within a fixed point.</summary>
        internal string ContentKey => ContentKeyFor(observations: null);

        internal string ContentKeyFor(FrontEndTraversalObservations? observations)
        {
            var key = PendingReference.KeyParts([
                FrontEndRegionKeys.NameSet(RequiredAncestorOwnedParameterNames),
                FrontEndRegionKeys.NameSet(VisiblePropertyDependencyNames),
                FrontEndRegionKeys.NameSet(PendingReferences.Select(static pending => pending.ContentKey)),
                FrontEndRegionKeys.NameSet(OwnerQualifiedParameters.Select(static r => r.ContentKey))]);
            observations?.RecordSummaryKey(key);
            return key;
        }
    }

    /// <summary>
    /// The completed summary of one algorithm node under the empty locally-owned context: the
    /// requirements of its OUTPUT (what evaluating the algorithm's value needs) and, per
    /// declared property, that member's requirements expanded through the algorithm's own
    /// sibling fixed point (relative to the algorithm's declaring level). The member seeds are
    /// what structural navigation (<c>Inner.X</c>) and <c>open</c>-provided names charge.
    /// Both are stored pristine; readers clone before accumulating.
    /// </summary>
    internal sealed class AlgorithmSummary(
        SummarySeed outputSeed,
        IReadOnlyDictionary<string, SummarySeed> memberSeeds)
    {
        public SummarySeed OutputSeed { get; } = outputSeed;

        public IReadOnlyDictionary<string, SummarySeed> MemberSeeds { get; } = memberSeeds;

        public static readonly IReadOnlyDictionary<string, SummarySeed> NoMembers =
            new Dictionary<string, SummarySeed>(StringComparer.Ordinal);
    }

    /// <summary>
    /// Completed-summary memo for the summary channel, keyed by ALGORITHM node REFERENCE
    /// (reference identity, like every other front-end memo: two structurally equal but
    /// distinct nodes summarize independently, while host-DAG sharing is by reference). An
    /// entry is the finished summary of <c>CollectSummarySeed(algorithm, empty locally-owned
    /// names)</c>, which is a pure function of the node: the summary walk never queries what
    /// ancestors own — a free parameter reference is reported as a required ancestor-owned
    /// name regardless of the ancestor context — so the empty-locals summary carries no
    /// caller state. Conditional BRANCH bodies summarize under their per-branch binder names
    /// (a genuinely context-sensitive input) and therefore never pass through this memo.
    /// Entries are admitted only AFTER a summary is fully computed (local fixed point
    /// converged, self-owned parameters stripped); the structural preflight guarantees
    /// acyclic inputs, so a node can never be reached again while its own summary is still
    /// in flight. Lifetime is the caller's: <see cref="PropertyExposureResolver"/> creates
    /// ONE memo per resolution (never static, never cross-run) so each context-independent
    /// summary is computed once per resolution instead of once per ancestor level, and a
    /// standalone <see cref="BuildSummaries"/> call creates its own. Stored seeds follow the
    /// clone discipline documented on <see cref="SummarySeed"/>.
    /// </summary>
    internal sealed class SummaryMemo(FrontEndTraversalObservations? observations = null)
    {
        internal long ExpansionCycleCuts;
        internal Dictionary<(string Left, string Right), ResolvedOpenCandidate>? UnitedCandidates;

        internal readonly BranchContextInterner BranchContexts = new();
        private readonly Dictionary<Algorithm, CompletedStructureContext> _analysisContexts = new(ReferenceEqualityComparer.Instance);
        internal CompletedStructureContext AnalysisContextOf(Algorithm body)
        {
            if (!_analysisContexts.TryGetValue(body, out var context))
                _analysisContexts.Add(body, context = AnalyzedStaticStructures.ForBoundAst(body));
            return context;
        }
        // Completed requirements carry an exact origin until exposure settlement. Their summaries
        // are occurrence-contextual; the legacy pure node-keyed cache remains separate.
        internal Dictionary<(StaticLookupFacts Facts, StaticScopeKey Key), AlgorithmSummary>? ContextualAlgorithmSummaries;
        // Pure Q8 equations stay relative to their caller. This cache answers no structural question.
        internal Dictionary<Algorithm, AlgorithmSummary>? SymbolicAlgorithmSummaries;

        // A summary that neither observed nor captured a contextual selection is a symbolic
        // computation over the immutable body, not over the path by which it was reached.
        // ContextUses is a transitive effect: anchoring an escaping reference, observing a
        // selection, or reading a context-dependent cached result prevents independent reuse.
        // Keep this cache separate from summaries built without an admitted context: their
        // escaping names still need an origin when consumed by a contextual walk.
        internal Dictionary<Algorithm, AlgorithmSummary>? IndependentAlgorithmSummaries;
        internal Dictionary<BranchBodySummaryKey, SummarySeed>? IndependentBranchSummaries;
        internal Dictionary<OutputBundle, SummarySeed>? IndependentArgumentBundles;
        internal long ContextUses;
        internal void UseContext() => ContextUses++;

        internal bool BranchParametersAgree(Algorithm body, IReadOnlySet<string> binders,
            CompletedStructureContext context)
        {
            var parameters = context.Facts.Facts(context.Key)?.Parameters;
            if (parameters is null) return false;
            var own = ParameterNamesOf(body, observations);
            return parameters.Count == own.Count + binders.Count - binders.Count(own.Contains)
                && own.All(parameters.Contains) && binders.All(parameters.Contains);
        }

        private readonly Dictionary<object, bool> _bindingFree = new(ReferenceEqualityComparer.Instance);
        private readonly Dictionary<(StaticLookupFacts Facts, StaticScopeKey Parent, Algorithm Body),
            List<CompletedStructureContext>> _bindingFreeRegions = new();

        // A binder-free branch introduces no binding identity to rename. The same immutable
        // binding-free subtree under the exact same parent is therefore the same Q8 equation
        // environment, even when literal patterns give it distinct structural graph keys.
        // This is only a summary representative: the actual keys/publications and runtime
        // branch scopes remain distinct. Unknown stays Unknown; availability must agree.
        internal CompletedStructureContext? SummaryRegion(CompletedStructureContext? context, Algorithm body)
        {
            context = RequirementContext(context, body);
            if (context is not { Key.BindingRegion: not null, Key.Parent: { } parent } at
                || at.Facts.Facts(at.Key) is not { Body: { } view, Parameters.Count: 0 } facts
                || !ReferenceEquals(view, body) || !BindingFree(body)) return context;
            var key = (at.Facts, parent, body);
            if (!_bindingFreeRegions.TryGetValue(key, out var regions))
                _bindingFreeRegions.Add(key, regions = []);
            foreach (var previous in regions)
            {
                var before = previous.Facts.Facts(previous.Key)!;
                if (ReferenceEquals(before.Body, body) && before.Parameters.Count == 0
                    && before.IsProvisional == facts.IsProvisional
                    && SameSelection(before.Receiver, previous.Key, facts.Receiver, at.Key)
                    && SameSelection(before.Open, previous.Key, facts.Open, at.Key)
                    && before.Providers.SequenceEqual(facts.Providers)
                    && SameNames(before.UnavailableOpenNames, facts.UnavailableOpenNames)
                    && SameNames(before.AmbiguousOpenNames, facts.AmbiguousOpenNames)) return previous;
            }
            regions.Add(at);
            return at;
        }

        private static bool SameNames(IReadOnlySet<string>? left, IReadOnlySet<string>? right)
            => ReferenceEquals(left, right) || left is not null && right is not null && left.SetEquals(right);

        private static bool SameSelection(CompletedStaticStructures.Selection left, StaticScopeKey leftScope,
            CompletedStaticStructures.Selection right, StaticScopeKey rightScope)
            => left.Kind == right.Kind && Equals(left.Identity, right.Identity)
                && (ReferenceEquals(left.Target, right.Target)
                    || ReferenceEquals(left.Target, leftScope) && ReferenceEquals(right.Target, rightScope));

        private bool BindingFree(Algorithm body)
        {
            if (_bindingFree.TryGetValue(body, out var known)) return known;
            var pending = new Stack<object>();
            var seen = new HashSet<object>(ReferenceEqualityComparer.Instance);
            pending.Push(body);
            while (pending.TryPop(out var node))
            {
                if (!seen.Add(node)) continue;
                if (_bindingFree.TryGetValue(node, out known))
                {
                    if (known) continue;
                    return _bindingFree[body] = false;
                }
                if (node is Algorithm.User { ParameterPatterns.Count: > 0 }
                    || node is Algorithm.Conditional family && family.Branches.Any(branch => branch.Pattern.BoundNames().Any()))
                    return _bindingFree[body] = false;
                for (var i = 0; AstStructuralPreflight.TryGetChild(node, i, out var child); i++) pending.Push(child);
            }
            foreach (var node in seen) _bindingFree[node] = true;
            return true;
        }

        private readonly Dictionary<StaticLookupFacts, ElaboratedPropertyScope> _lookupRoots = new(ReferenceEqualityComparer.Instance);
        private readonly Dictionary<(StaticLookupFacts Facts, StaticScopeKey Key), Algorithm> _requirementViews = new();
        private readonly Dictionary<(StaticLookupFacts Facts, StaticScopeKey Key), ElaboratedPropertyScope> _requirementLevels = new();
        private readonly Dictionary<StaticLookupFacts, RequirementLookupFacts> _requirementFacts = new(ReferenceEqualityComparer.Instance);

        internal CompletedStructureContext? RequirementContext(CompletedStructureContext? context, Algorithm? body = null)
        {
            if (context is not { } at) return null;
            var source = at.Facts is RequirementLookupFacts existing ? existing.Source : at.Facts;
            if (source is not CompletedStaticStructures { HasProvisional: true }) return at;
            if (!_requirementFacts.TryGetValue(source, out var projection))
                _requirementFacts.Add(source, projection = new(source, _requirementViews));
            if (body is not null && source.Facts(at.Key)?.IsProvisional == true)
            {
                if (!ReferenceEquals(OpenProviderIdentity.DeclarationOf(body), at.Key.Declaration))
                    throw new InvalidOperationException("A provisional requirement frame must preserve its admitted declaration.");
                if (_requirementViews.TryAdd((source, at.Key), body)) projection.Revision++;
            }
            return projection.Context(at.Key);
        }

        // A Q8-only view of genuine Q1-Q7 answers plus the provisional tree the summary walk
        // received. It creates no answer, changes no completion eligibility and never escapes
        // the summary memo into a program, continuation or runtime activation.
        private sealed class RequirementLookupFacts(StaticLookupFacts source,
            Dictionary<(StaticLookupFacts Facts, StaticScopeKey Key), Algorithm> views) : StaticLookupFacts
        {
            internal StaticLookupFacts Source => source;
            internal int Revision;
            private int _cachedVersion = -1;
            private readonly Dictionary<StaticScopeKey, CompletedStaticStructures.BodyFacts> _projected = new(ReferenceEqualityComparer.Instance);
            internal override StaticScopeKey PreludeKey => source.PreludeKey;
            internal override IEnumerable<StaticScopeKey> Scopes => source.Scopes;
            internal override int ViewVersion => unchecked(source.ViewVersion + Revision);
            internal override void EnsureUsable() => source.EnsureUsable();
            internal override StaticScopeKey? Child(StaticScopeKey parent, Algorithm body, Pattern? pattern = null) => source.Child(parent, body, pattern);
            internal override CompletedStaticStructures.BodyFacts? Facts(StaticScopeKey key)
            {
                if (_cachedVersion != source.ViewVersion) { _projected.Clear(); _cachedVersion = source.ViewVersion; }
                if (_projected.TryGetValue(key, out var known)) return known;
                var facts = source.Facts(key);
                if (facts is not { IsProvisional: true } || !views.TryGetValue((source, key), out var body)) return facts;
                return _projected[key] = facts with { Body = body,
                    Receiver = facts.RequirementReceiver ?? CompletedStaticStructures.Selection.Unavailable,
                    Open = facts.RequirementOpen ?? CompletedStaticStructures.Selection.Unavailable };
            }
        }

        private ElaboratedPropertyScope LookupScope(CompletedStructureContext origin)
            => RequirementLevel(origin);

        internal ElaboratedPropertyScope RequirementLevel(CompletedStructureContext origin)
        {
            origin = RequirementContext(origin)!;
            if (!_lookupRoots.TryGetValue(origin.Facts, out var root))
            {
                root = ElaboratedScopeLookup.CreateScope(origin.Facts.Prelude,
                    completedContext: origin.Facts.Context(origin.Facts.PreludeKey),
                    memberIndexes: new OpenMemberIndexCache(observations), observations: observations);
                _lookupRoots.Add(origin.Facts, root);
                _requirementLevels.Add((origin.Facts, origin.Facts.PreludeKey), root);
            }
            var pending = new Stack<StaticScopeKey>();
            var key = origin.Key;
            while (!_requirementLevels.ContainsKey((origin.Facts, key)))
            {
                pending.Push(key);
                key = key.Parent ?? throw new InvalidOperationException("A requirement frame must reach its admitted prelude.");
            }
            var level = _requirementLevels[(origin.Facts, key)];
            while (pending.TryPop(out key))
            {
                var facts = origin.Facts.Facts(key);
                var body = facts?.Body
                    ?? throw new InvalidOperationException("An unavailable requirement frame has no admitted provisional view.");
                level = ElaboratedScopeLookup.CreateScope(body, level, observations: observations,
                    memberIndexes: root.MemberIndexes, completedContext: origin.Facts.Context(key));
                _requirementLevels.Add((origin.Facts, key), level);
            }
            return level;
        }

        internal PendingReference SelectedReference(PendingReference reference)
        {
            if (reference.Origin is not null) UseContext();
            if (reference is not { Origin: { } origin, OpenPath: false, Candidates.Count: 0 }
                || origin.Facts.Facts(origin.Key)?.Body is null) return reference;
            var scope = LookupScope(origin);
            var owned = ElaboratedScopeLookup.SelectOwnedDeclaration(scope, reference.Head, ElaboratedScopeLookup.OwnParameterBindings.Instance);
            CompletedStructureContext? selected = null;
            if (owned.TryGetProperty(out var declaring, out _)) selected = declaring.CompletedContext;
            else if (owned.Kind == OwnedDeclarationKind.None && reference.Members.Count == 0)
            {
                // Navigating an opened head checks that member's accessibility before its
                // children. Keep its opening origin so settlement charges the head as well
                // as the remaining path. A lexical head at the provider would skip it.
                // A partial provider list cannot select an identity. Name presence alone never
                // licenses this bridge, even when one currently published provider offers it.
                for (var at = scope; at is not null; at = at.Parent)
                    if (at.CompletedContext is not { } context || context.Facts.Facts(context.Key) is not { Body: not null } facts
                        || facts.Providers.Any(provider => provider.Kind == StaticFactKind.Unknown)) return reference;
                selected = ElaboratedScopeLookup.LookupSingleOpenMember(scope, reference.Head)?.MemberLevel.CompletedContext;
            }
            return selected is null || ReferenceEquals(selected.Key, origin.Key) ? reference
                : new(reference.Head, reference.Members, reference.Candidates, reference.BoundOwners, selected);
        }

        // Project a completed Q1 owner selection onto THIS live Q8 equation map. Context-bearing
        // paths, open choices and bound-owner exclusions keep their full symbolic representation.
        internal bool SelectsLocalMember(PendingReference reference, CompletedStructureContext level)
        {
            if (reference.Origin is not null) UseContext();
            if (reference is not { Origin: { } origin, OpenPath: false, Members.Count: 0, Candidates.Count: 0, BoundOwners.Count: 0 }
                || !ReferenceEquals(origin.Facts, level.Facts) || origin.Facts.Facts(origin.Key)?.Body is null)
                return false;
            var scope = LookupScope(origin);
            var selected = ElaboratedScopeLookup.SelectOwnedDeclaration(scope, reference.Head, ElaboratedScopeLookup.OwnParameterBindings.Instance);
            return selected.TryGetProperty(out var declaring, out var hit)
                && ReferenceEquals(declaring.CompletedContext?.Key, level.Key)
                && ReferenceEquals(level.Facts.Member(level.Key, reference.Head), declaring.CompletedContext!.Facts.Member(level.Key, hit.Property.Name));
        }

        internal FrontEndTraversalObservations? Observations => observations;

        // Pure anchoring of an immutable completed seed. The exact source version and the entire
        // intervening owner path (declaring -> ancestor) decide it; no live requirement set is cached.
        internal Dictionary<(StaticLookupFacts Facts, int Version, SummarySeed Seed, StaticScopeKey? Declaring,
            StaticScopeKey Ancestor), SummarySeed>? AnchoredRequirements;

        /// <summary>
        /// EXPOSURE-OPEN-1: the interner of resolved open candidates' deep facts
        /// (<see cref="ResolvedOpenCandidate.Facts"/>), one per memo lifetime like every key below.
        /// </summary>
        internal SeedFactInterner SeedFacts => _seedFacts ??= new(observations);

        private SeedFactInterner? _seedFacts;

        private Dictionary<string, int>? _seedKeyIds;

        /// <summary>
        /// EXPOSURE-OPEN-1: the analysis-local id of a candidate seed's EXACT content key (a dictionary
        /// over the full string — never a hash of it). A candidate's own key names its seed by this id,
        /// so a key enclosing a nested candidate costs that candidate's id, not its serialization.
        /// </summary>
        internal int SeedKeyId(string seedContentKey)
        {
            var ids = _seedKeyIds ??= new(StringComparer.Ordinal);
            if (!ids.TryGetValue(seedContentKey, out var id))
                ids.Add(seedContentKey, id = ids.Count);
            return id;
        }

        private Dictionary<OpenProviderIdentity, int>? _providerIdentityKeys;

        /// <summary>
        /// The analysis-local key of an open provider identity (Q-19 D-I): equal identities share
        /// one key, so a candidate's content key distinguishes providers exactly as identity does.
        /// </summary>
        internal int ProviderIdentityKey(OpenProviderIdentity identity)
        {
            var keys = _providerIdentityKeys ??= new();
            if (!keys.TryGetValue(identity, out var key))
                keys.Add(identity, key = keys.Count);
            return key;
        }

        /// <summary>
        /// Completed contextual branch computations retain their exact binding-region key.
        /// A computation certified free of contextual effects goes instead into
        /// <see cref="IndependentBranchSummaries"/>, by body reference and binder-name set,
        /// after agreement with the authoritative parameter facts. Ordinary property summaries
        /// use a separate cache. All stored seeds follow the same pristine-clone discipline.
        /// </summary>
        internal Dictionary<BranchBodySummaryKey, SummarySeed>? CompletedBranchBodySummaries;

        /// <summary>
        /// Seeds of expressions walked in the TRANSPARENT context (argument slots and capture rows:
        /// empty local summaries, nothing owned), by node reference. That context is the same in
        /// every region, so such a seed is a pure function of the node and is computed once per
        /// memo lifetime — never once per owner region (FE-3: K owners sharing one synthesized
        /// argument bundle summarize it once). Stored pristine; readers clone.
        /// </summary>
        internal Dictionary<Expr, SummarySeed>? TransparentSeeds;

        /// <summary>
        /// Completed call and dot-call argument-bundle seeds, by bundle reference (FE-2): a pure
        /// function of the bundle (the transparent walk), kept for the memo lifetime (FE-3).
        /// </summary>
        internal Dictionary<OutputBundle, SummarySeed>? ArgumentBundleSeeds;

        /// <summary>
        /// FE-3: whether a COMPLETED seed carries nothing but required names that an owner's name
        /// set covers, by (seed, set) reference pair — see <see cref="SummarySeed.DropOwnedAbsorbedParts"/>.
        /// </summary>
        internal Dictionary<(SummarySeed Part, IReadOnlySet<string> Owned), bool>? OwnedPureParts;

        internal bool IsOwnedPureRequirement(SummarySeed part, IReadOnlySet<string> owned)
        {
            // A composed owner signature's names are its owner-local head over a SHARED tail: the part
            // is decided against the tail once (per part and tail), and only the names the tail does not
            // cover are tested against this owner's own set — never the part's full width per owner.
            if (owned is ImplicitSignatureTemplate.NameSetView { Tail: { } tail })
            {
                if (ResidualOf(part, tail) is not { } residual)
                    return false;
                foreach (var name in residual)
                {
                    observations?.RecordSummaryResidualNameProbe();
                    if (!owned.Contains(name))
                        return false;
                }

                return true;
            }

            OwnedPureParts ??= new(OwnedPartKeyComparer.Instance);
            if (!OwnedPureParts.TryGetValue((part, owned), out var pure))
            {
                pure = part.IsPureRequirementWithin(owned, observations);
                OwnedPureParts.Add((part, owned), pure);
            }

            return pure;
        }

        private Dictionary<(SummarySeed Part, IReadOnlySet<string> Owned), string[]?>? _residuals;

        // The required names of a pure-requirement part that a tail name set does not cover (null
        // when the part carries anything but required names), once per (part, tail).
        private string[]? ResidualOf(SummarySeed part, IReadOnlySet<string> tail)
        {
            _residuals ??= new(OwnedPartKeyComparer.Instance);
            if (!_residuals.TryGetValue((part, tail), out var residual))
            {
                residual = part.RequiredNamesOutside(tail, ResidualOf, observations);
                _residuals.Add((part, tail), residual);
            }

            return residual;
        }

        private sealed class OwnedPartKeyComparer : IEqualityComparer<(SummarySeed Part, IReadOnlySet<string> Owned)>
        {
            public static readonly OwnedPartKeyComparer Instance = new();

            public bool Equals((SummarySeed Part, IReadOnlySet<string> Owned) x, (SummarySeed Part, IReadOnlySet<string> Owned) y)
                => ReferenceEquals(x.Part, y.Part) && ReferenceEquals(x.Owned, y.Owned);

            public int GetHashCode((SummarySeed Part, IReadOnlySet<string> Owned) key)
                => HashCode.Combine(
                    System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(key.Part),
                    System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(key.Owned));
        }

        private Dictionary<Algorithm, IReadOnlySet<string>>? _ownerParameterNames;

        private static readonly IReadOnlySet<string> NoParameterNames = new HashSet<string>(StringComparer.Ordinal);

        /// <summary>
        /// <paramref name="owner"/>'s parameter NAMES, materialized once per memo lifetime (FE-1):
        /// every property summary, fixed-point iteration, and requirement strip at that owner
        /// shares this one set instead of re-reading the owner's live <c>Params</c> projection —
        /// W names allocated and scanned per property made an owner of W parameters and K
        /// properties cost K × W. Keyed by node reference: the pass never rewrites a node's
        /// parameter list while summarizing it, and a host AST is not mutated during analysis.
        /// </summary>
        internal IReadOnlySet<string> ParameterNamesOf(Algorithm owner, FrontEndTraversalObservations? observations)
        {
            if (owner is not Algorithm.User { ParameterPatterns.Count: > 0 } user)
                return NoParameterNames;

            // A shared implicit-signature template (FE-3) already holds its name set: every owner of
            // the template reads that one set instead of materializing its own.
            if (user.ParameterPatterns is ImplicitSignatureTemplate template)
                return template.Facts.NameSet;

            _ownerParameterNames ??= new(ReferenceEqualityComparer.Instance);
            if (!_ownerParameterNames.TryGetValue(owner, out var names))
            {
                var parameters = owner.Params;
                observations?.RecordOwnerParameterNamesMaterialized(parameters.Count);
                names = new HashSet<string>(parameters, StringComparer.Ordinal);
                _ownerParameterNames.Add(owner, names);
            }

            return names;
        }
    }

    /// <summary>Key of <see cref="SummaryMemo.CompletedBranchBodySummaries"/>: body by reference, binders by content.</summary>
    internal sealed record BranchBodySummaryKey(Algorithm Body, int BinderNames, StaticScopeKey? Scope = null,
        StaticLookupFacts? Facts = null)
    {
        public bool Equals(BranchBodySummaryKey? other)
            => other is not null && ReferenceEquals(Body, other.Body) && BinderNames == other.BinderNames
                && ReferenceEquals(Scope, other.Scope) && ReferenceEquals(Facts, other.Facts);

        public override int GetHashCode()
            => HashCode.Combine(System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(Body), BinderNames, Scope, Facts);
    }

    /// <summary>
    /// Reference-identity memo state for ONE summary-collection region (one algorithm-level
    /// analysis, or one <see cref="BuildSummaries"/> call's top property loop): the walk's
    /// two context flavors get separate expression maps — the region's PRIMARY (its local
    /// summaries and owned-here names) and the TRANSPARENT bundle context (empty summaries,
    /// empty owned-here — call/dot-call argument bundles and capture rows, identical however
    /// deeply they nest). Stored seeds follow a CLONE discipline: callers mutate returned
    /// seeds as accumulators, so a memo keeps a pristine clone and every reach (first or
    /// later) receives its own mutable copy — semantically identical to re-walking the
    /// equivalent duplicated tree, because seed contributions are name SETS. Whole
    /// nested-algorithm summaries (property values and <see cref="Expr.AlgorithmExpr"/>
    /// contents alike, all summarized under the empty locally-owned context) live on the
    /// region-spanning <see cref="SharedMemo"/> instead, so they are computed once per memo
    /// lifetime rather than once per region; conditional BRANCH bodies stay exempt (their
    /// binder-name context varies per branch).
    /// </summary>
    internal sealed class SummaryWalkMemos(SummaryMemo sharedMemo, FrontEndTraversalObservations? observations,
        CompletedStructureContext? completedContext = null)
    {
        public CompletedStructureContext? CompletedContext = completedContext;
        public Dictionary<Expr, SummarySeed>? TransparentSeeds;
        public Dictionary<OutputBundle, SummarySeed>? ArgumentBundleSeeds;
        public Dictionary<Expr, SummarySeed>? PrimarySeeds;

        public readonly SummaryMemo SharedMemo = sharedMemo;

        public readonly FrontEndTraversalObservations? Observations = observations;
    }

    /// <summary>
    /// The context ONE level offers to the seeds escaping from inside it: the level's
    /// algorithm (its properties for navigation, its <c>open</c> targets as candidates) and
    /// its current local property summaries. Used by the builder for every nested level and
    /// by the exposure resolver when it expands a navigated member's seed through the
    /// algorithms of a member path.
    /// </summary>
    internal sealed class LevelContext(
        Algorithm algorithm,
        IReadOnlyDictionary<string, SummarySeed> localPropertySummaries,
        SummaryWalkMemos memos)
    {
        public Algorithm Algorithm { get; } = algorithm;

        public IReadOnlyDictionary<string, SummarySeed> LocalPropertySummaries { get; } = localPropertySummaries;

        public SummaryWalkMemos Memos { get; } = memos;

        // Only the dynamic extent of ONE ExpandAtLevel call at this exact level. The member map
        // cannot grow during an equation's evaluation; the next evaluation starts with no cache.
        internal Dictionary<string, SummarySeed>? ExpandedSeeds;

        public bool HasOpens => Algorithm.Opens.Count > 0;

        /// <summary>The level algorithm's parameter names, shared through the resolution's memo.</summary>
        public IReadOnlySet<string> ParameterNames => Memos.CompletedContext is { Key.BindingRegion: not null } context
            ? context.Facts.Facts(context.Key)?.Parameters ?? Memos.SharedMemo.ParameterNamesOf(Algorithm, Memos.Observations)
            : Memos.SharedMemo.ParameterNamesOf(Algorithm, Memos.Observations);
    }

    /// <summary>
    /// Reference-identity memo for ONE sibling-dependency collection (one property's value
    /// subtree): contributions are an index SET, so a completed node reference — split by the
    /// two context dimensions that change a node's contribution, the shadow context of the
    /// nested bodies around it and its position (value, callee, transparent) — is skipped,
    /// and a nested body reached again under the same shadow context is not re-walked.
    /// </summary>
    private sealed class SiblingWalkMemo(FrontEndTraversalObservations? observations)
    {
        internal readonly Dictionary<Algorithm, CanonicalNameSet> OwnShadowNames = new(ReferenceEqualityComparer.Instance);
        internal readonly Dictionary<(int Context, Algorithm Body), ShadowScope> EnteredShadows = new(new ShadowEntryComparer());

        private sealed class ShadowEntryComparer : IEqualityComparer<(int Context, Algorithm Body)>
        {
            public bool Equals((int Context, Algorithm Body) x, (int Context, Algorithm Body) y)
                => x.Context == y.Context && ReferenceEquals(x.Body, y.Body);
            public int GetHashCode((int Context, Algorithm Body) value)
                => HashCode.Combine(value.Context, System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(value.Body));
        }
        private readonly Dictionary<(int Shadow, LiftingRole Role), HashSet<Expr>> _visited = new();

        private readonly Dictionary<int, HashSet<Algorithm>> _algorithms = new();

        public readonly FrontEndTraversalObservations? Observations = observations;

        public HashSet<Expr> Visited(int shadowKey, LiftingRole position)
        {
            if (!_visited.TryGetValue((shadowKey, position), out var visited))
                _visited[(shadowKey, position)] = visited = new HashSet<Expr>(ReferenceEqualityComparer.Instance);
            return visited;
        }

        public HashSet<Algorithm> Algorithms(int shadowKey)
        {
            if (!_algorithms.TryGetValue(shadowKey, out var visited))
                _algorithms[shadowKey] = visited = new HashSet<Algorithm>(ReferenceEqualityComparer.Instance);
            return visited;
        }
    }

    /// <summary>
    /// Sibling/processing-order channel: per-property direct sibling dependency edges (and,
    /// lazily, the topological order derived from them). Deliberately computes NO summary
    /// data — the implicit-argument resolver consumes only this channel, and the recursive
    /// summary fixed-point was pure dead work on its path (M17).
    /// </summary>
    public static PropertyDependencyGraph BuildDependencyOrder(
        Algorithm.User algorithm,
        Func<string, bool>? preludeNameShadowedByCaller = null,
        FrontEndTraversalObservations? observations = null,
        SiblingOrderLookup? lookup = null)
    {
        var propertyNameToIndex = new Dictionary<string, int>(StringComparer.Ordinal);
        for (var i = 0; i < algorithm.Properties.Count; i++)
            propertyNameToIndex[algorithm.Properties[i].Name] = i;

        var siblingNames = new HashSet<string>(propertyNameToIndex.Keys, StringComparer.Ordinal);
        IReadOnlySet<string> ownedHere = algorithm.ParameterPatterns is ImplicitSignatureTemplate template
            ? template.Facts.NameSet
            : CreateNameSet(algorithm.Params);

        // Whether a prelude name is shadowed at this level through ordinary
        // resolution: siblings, this algorithm's own parameters, and
        // the caller-supplied ancestor knowledge (the implicit-argument
        // resolver passes its visible property map's membership test). Math
        // alias calls and canonical `Math.X` calls both consult this so the
        // sibling-order channel has the SAME binding knowledge as rewriting. A
        // PREDICATE, not a materialized union: copying the ancestor map's keys
        // per build call is O(ancestor properties) for every processed
        // property value and made wide flat scopes quadratic.
        bool PreludeNameShadowed(string name)
            => siblingNames.Contains(name)
                || ownedHere.Contains(name)
                || (preludeNameShadowedByCaller?.Invoke(name) ?? false);

        // One interner for every property walk of this build: shadow keys are canonical ids (FE-1).
        var shadowNames = new NameSetInterner(observations);
        var nodes = new PropertyDependencyNode[algorithm.Properties.Count];
        for (var i = 0; i < algorithm.Properties.Count; i++)
        {
            // Every value-position sibling reference in the property's whole value subtree
            // — output rows, nested property values, block literals, capture rows, and
            // conditional branch bodies alike — is a processing-order dependency, because the
            // resolver rewrites all of it while processing this property.
            var dependencyIndices = new HashSet<int>();
            var softDependencyIndices = new HashSet<int>();
            CollectAlgorithmSiblingDependencyIndices(
                algorithm.Properties[i].Value,
                new SiblingWalkContext(siblingNames, propertyNameToIndex, dependencyIndices, i, new SiblingWalkMemo(observations), lookup)
                {
                    SoftDependencyIndices = softDependencyIndices,
                },
                ShadowScope.Level(shadowNames, PreludeNameShadowed));
            softDependencyIndices.ExceptWith(dependencyIndices);
            nodes[i] = new PropertyDependencyNode(i, dependencyIndices.OrderBy(static idx => idx).ToArray())
            {
                SoftSiblingDependencyIndices = softDependencyIndices.OrderBy(static idx => idx).ToArray(),
            };
        }

        return new PropertyDependencyGraph(algorithm.Properties, propertyNameToIndex, nodes);
    }

    /// <summary>
    /// Recursive summary channel: per-property recursive ancestor-capture facts for the
    /// exposure resolver. Deliberately computes NO sibling/order data (M17). A
    /// caller-supplied <paramref name="memo"/> extends completed-summary reuse across every
    /// <see cref="BuildSummaries"/> call of one logical analysis (the exposure resolver
    /// passes one memo per resolution, so a nested algorithm's summary is computed once
    /// rather than once per ancestor level); with no memo the call is standalone and
    /// creates its own.
    /// </summary>
    public static PropertyDependencySummaryGraph BuildSummaries(
        Algorithm algorithm,
        SummaryMemo? memo = null,
        FrontEndTraversalObservations? observations = null,
        CompletedStructureContext? completedContext = null)
    {
        memo ??= new SummaryMemo(observations);
        if (completedContext is null && HasStructuralSelectionQuestion(algorithm))
            completedContext = memo.AnalysisContextOf(algorithm);
        var propertyNameToIndex = new Dictionary<string, int>(StringComparer.Ordinal);
        for (var i = 0; i < algorithm.Properties.Count; i++)
            propertyNameToIndex[algorithm.Properties[i].Name] = i;

        // One memo bundle spans the whole BuildSummaries call: every property value below is
        // summarized under the same empty locally-owned context, so two properties sharing
        // ONE value algorithm summarize it once — and the caller's shared memo carries the
        // same completed summaries across nesting levels.
        var buildMemos = new SummaryWalkMemos(memo ?? new SummaryMemo(observations), observations, completedContext);
        var nodes = new PropertyDependencySummaryNode[algorithm.Properties.Count];
        for (var i = 0; i < algorithm.Properties.Count; i++)
        {
            var summarySeed = CollectSharedAlgorithmSummarySeed(algorithm.Properties[i].Value, buildMemos);
            var summarySiblingDependencyIndices = new HashSet<int>();
            var summaryVisiblePropertyDependencyNames = CreateNameSet();
            foreach (var dependencyName in summarySeed.VisiblePropertyDependencyNames)
            {
                if (propertyNameToIndex.TryGetValue(dependencyName, out var dependencyIndex)
                    && dependencyIndex != i)
                    summarySiblingDependencyIndices.Add(dependencyIndex);
                else
                    summaryVisiblePropertyDependencyNames.Add(dependencyName);
            }

            nodes[i] = new PropertyDependencySummaryNode(
                i,
                summarySiblingDependencyIndices.OrderBy(static idx => idx).ToArray(),
                summaryVisiblePropertyDependencyNames.OrderBy(static name => name, StringComparer.Ordinal).ToArray(),
                summarySeed.RequiredAncestorOwnedParameterNames.OrderBy(static name => name, StringComparer.Ordinal).ToArray(),
                summarySeed.PendingReferences.Select(buildMemos.SharedMemo.SelectedReference)
                    .Distinct().OrderBy(static pending => pending.ContentKey, StringComparer.Ordinal).ToArray(),
                summarySeed.OwnerQualifiedParameters.ToArray());
        }

        return new PropertyDependencySummaryGraph(algorithm.Properties, propertyNameToIndex, nodes);
    }

    /// <summary>A capability gate only: ordinary symbolic Q8 equations require no Q1–Q7 selection.</summary>
    private static bool HasStructuralSelectionQuestion(Algorithm algorithm)
    {
        var declarations = BuiltinRegistry.CreateSemanticPreludeAlgorithm().Properties.Select(property => property.Name).ToHashSet(StringComparer.Ordinal);
        var heads = new HashSet<string>(StringComparer.Ordinal);
        var seen = new HashSet<object>(ReferenceEqualityComparer.Instance);
        var pending = new Stack<object>();
        pending.Push(algorithm);
        while (pending.TryPop(out var node))
        {
            if (!seen.Add(node)) continue;
            if (node is Algorithm body)
            {
                if (body.Opens.Count != 0) return true;
                foreach (var property in body.Properties)
                {
                    declarations.Add(property.Name);
                    pending.Push(property.Value);
                }
                if (body is Algorithm.Conditional family)
                    foreach (var branch in family.Branches) pending.Push(branch.Body);
                foreach (var row in body.Output) pending.Push(row);
                // Parameter patterns contain no expressions or structural-selection questions.
                // The summary memo alone materializes their known owner-name set.
                continue;
            }
            if (node is Expr.DotCall edge && TryGetStaticMemberPath(edge, out var head, out _)) heads.Add(head);
            for (var i = 0; AstStructuralPreflight.TryGetChild(node, i, out var child); i++) pending.Push(child);
        }
        // Over-approximate the questions, never a selected binding, alias, receiver or provider.
        return heads.Overlaps(declarations);
    }

    private static CompletedStructureContext ChildContext(CompletedStructureContext parent, Algorithm body,
        Pattern? pattern = null, bool transparentFamily = false)
    {
        var facts = parent.Facts is AnalyzedStaticStructures ? parent.Facts : body.CompletedStructure?.Facts ?? parent.Facts;
        if (parent.Facts is not AnalyzedStaticStructures && body.CompletedStructure is { Entry: { } entry } publication)
            return publication.Facts.Context(entry);
        var declaring = transparentFamily ? parent.Key.Parent ?? facts.PreludeKey : parent.Key;
        var key = pattern is null && ReferenceEquals(facts.Facts(declaring)?.Body, body)
            ? declaring : facts.Child(declaring, body, pattern);
        return facts.Context(key ?? new StaticScopeKey(body.IsModuleRoot ? facts.PreludeKey : declaring,
            OpenProviderIdentity.DeclarationOf(body), pattern));
    }

    /// <summary>A fresh walk-memo bundle over a shared memo, for the exposure resolver's own charging calls.</summary>
    internal static SummaryWalkMemos CreateWalkMemos(SummaryMemo memo, FrontEndTraversalObservations? observations,
        CompletedStructureContext? completedContext = null)
        => new(memo, observations, completedContext);

    /// <summary>
    /// Memo-shared nested-algorithm summary for the constant empty locally-owned context —
    /// see <see cref="SummaryMemo"/> for why that summary is a pure function of the node
    /// reference and <see cref="SummarySeed"/> for the clone discipline. The observation
    /// counter records completed COMPUTATIONS (memo misses) only, so an observed analysis
    /// is pinned to at most one computation per distinct algorithm node per memo lifetime.
    /// </summary>
    private static SummarySeed CollectSharedAlgorithmSummarySeed(
        Algorithm algorithm,
        SummaryWalkMemos memos)
        => algorithm is Algorithm.User { IsAssignmentDeconstructionSource: true } source
            ? CollectSummarySeed(source.Output, new Dictionary<string, SummarySeed>(StringComparer.Ordinal),
                CreateNameSet(), memos, inTransparentContext: false)
            : GetAlgorithmSummary(algorithm, memos).OutputSeed.Clone();

    /// <summary>
    /// The completed summary of a node (output seed and per-member seeds), computed at most
    /// once per memo lifetime. Conditional families and builtins have no members.
    /// </summary>
    internal static AlgorithmSummary GetAlgorithmSummary(Algorithm algorithm, SummaryWalkMemos memos,
        CompletedStructureContext? exactContext = null)
    {
        if (exactContext is null && memos.CompletedContext is null)
        {
            var symbolic = memos.SharedMemo.SymbolicAlgorithmSummaries ??= new(ReferenceEqualityComparer.Instance);
            if (symbolic.TryGetValue(algorithm, out var known)) return known;
            memos.Observations?.RecordDependencyAlgorithmSummaryComputation();
            var summary = CollectAlgorithmSummary(algorithm, CreateNameSet(), memos.SharedMemo, memos.Observations);
            symbolic.Add(algorithm, summary);
            return summary;
        }
        var context = exactContext ?? (memos.CompletedContext is { } parent
            ? ChildContext(parent, algorithm) : memos.SharedMemo.AnalysisContextOf(algorithm));
        context = memos.SharedMemo.RequirementContext(context, algorithm)!;
        var independent = memos.SharedMemo.IndependentAlgorithmSummaries ??= new(ReferenceEqualityComparer.Instance);
        var canShare = context.Key.BindingRegion is null;
        if (canShare && independent.TryGetValue(algorithm, out var shared)) return shared;
        var cache = memos.SharedMemo.ContextualAlgorithmSummaries ??= new();
        var key = (context.Facts, context.Key);
        if (cache.TryGetValue(key, out var result))
        {
            memos.SharedMemo.UseContext();
            return result;
        }
        var uses = memos.SharedMemo.ContextUses;
        if (!canShare) memos.SharedMemo.UseContext();
        memos.Observations?.RecordDependencyAlgorithmSummaryComputation();
        result = CollectAlgorithmSummary(algorithm, CreateNameSet(), memos.SharedMemo, memos.Observations, context);
        if (uses == memos.SharedMemo.ContextUses) independent.Add(algorithm, result);
        else cache[key] = result;
        return result;
    }

    private static SummarySeed CollectSummarySeed(
        Algorithm algorithm,
        IReadOnlySet<string> locallyOwnedNames,
        SummaryMemo sharedMemo,
        FrontEndTraversalObservations? observations,
        CompletedStructureContext? completedContext = null)
        => CollectAlgorithmSummary(algorithm, locallyOwnedNames, sharedMemo, observations, completedContext).OutputSeed;

    private static AlgorithmSummary CollectAlgorithmSummary(
        Algorithm algorithm,
        IReadOnlySet<string> locallyOwnedNames,
        SummaryMemo sharedMemo,
        FrontEndTraversalObservations? observations,
        CompletedStructureContext? completedContext = null)
    {
        // Only the Q8 walk supplies this already detected provisional view. It is a lexical
        // requirement frame, never a successful structural body or a raw-reference fallback.
        completedContext = sharedMemo.RequirementContext(completedContext, algorithm);
        return algorithm switch
        {
            // A callable alias is summarized exactly like a body with no parameters whose one row
            // is its target reference: what the alias requires is what reading its target requires
            // (its exposure follows that read), and its own declarations are its only members.
            Algorithm.User or Algorithm.Alias => CollectScopeBodySummary(algorithm, locallyOwnedNames, sharedMemo, observations, completedContext),
            Algorithm.Conditional conditional => new AlgorithmSummary(
                CollectSummarySeed(conditional, locallyOwnedNames, sharedMemo, observations, completedContext),
                AlgorithmSummary.NoMembers),
            Algorithm.Builtin => new AlgorithmSummary(new SummarySeed(), AlgorithmSummary.NoMembers),
        };
    }

    /// <summary>
    /// The summary of a SCOPE BODY — a user algorithm, or a callable alias (whose output is its one
    /// target row and which declares no parameters) — read through the total accessors.
    /// </summary>
    private static AlgorithmSummary CollectScopeBodySummary(
        Algorithm algorithm,
        IReadOnlySet<string> locallyOwnedNames,
        SummaryMemo sharedMemo,
        FrontEndTraversalObservations? observations,
        CompletedStructureContext? completedContext = null)
    {
        // A synthetic assignment-deconstruction helper (`x, *y, z = RHS`) is self-contained: it
        // binds its own N-capture pattern and outputs one of those bound params, capturing no
        // ancestor-owned parameter and referencing no visible or sibling property (the shared
        // `$deconstruct$` source is referenced by the helper's ARGS, not the helper itself). Its
        // summary is therefore empty. Walking it costs O(N) per helper in its capture count
        // (the ownedHere union below and the fixed-point setup), so a wide deconstruction is
        // O(N^2) across its N sibling helpers without this leaf guard.
        if (algorithm is Algorithm.User { AssignmentDeconstructionTarget: not null })
            return new AlgorithmSummary(new SummarySeed(), AlgorithmSummary.NoMembers);

        var ownerParameterNames = sharedMemo.ParameterNamesOf(algorithm, observations);
        // The owned-here set is read only: with no locally owned names it IS the owner's parameter
        // set (a template owner's shared set), never a per-owner copy of it (FE-3).
        IReadOnlySet<string> ownedHere;
        if (locallyOwnedNames.Count == 0)
        {
            ownedHere = ownerParameterNames;
        }
        else
        {
            var union = CreateNameSet(locallyOwnedNames);
            union.UnionWith(ownerParameterNames);
            ownedHere = union;
        }

        // Ownership attribution follows the same transparency model as
        // ParameterDetector: transparent OutputBundle content (call/dot-call
        // argument bundles, surviving parenthesized groups) owns no names, so
        // its walk uses the enclosing algorithm's owned-name set. A parameter
        // reference inside such a layer therefore seeds the same
        // ancestor-capture requirement as the identical reference written
        // directly in the enclosing owner; the final
        // RemoveRequiredAncestorOwnedParameterNames strip below keeps each
        // algorithm's self-owned parameters out of the summary it returns. What
        // ancestors own is deliberately NOT an input: a parameter reference not
        // owned within this walk is reported as a required ancestor-owned name
        // regardless, which is what makes the empty-locals summary a pure
        // function of the node (see SummaryMemo).

        // One expression-memo bundle per algorithm-level analysis region: the property base
        // seeds and the opens/output walks below all run against this region's local-summary
        // and owned-here context (property values and nested AlgorithmExpr contents go
        // through the shared completed-summary memo instead).
        var memos = new SummaryWalkMemos(sharedMemo, observations, completedContext);
        var currentPropertySummaries = new Dictionary<string, SummarySeed>(StringComparer.Ordinal);
        var propertyBaseSeeds = new SummarySeed[algorithm.Properties.Count];
        for (var i = 0; i < algorithm.Properties.Count; i++)
        {
            var property = algorithm.Properties[i];
            currentPropertySummaries[property.Name] = new SummarySeed();
            propertyBaseSeeds[i] = CollectSharedAlgorithmSummarySeed(property.Value, memos);
        }

        if (propertyBaseSeeds.Length > 0)
            SolveMemberSeeds(algorithm, propertyBaseSeeds, currentPropertySummaries, memos);

        var seed = CollectOpenTargetSeeds(algorithm.Opens, currentPropertySummaries, ownedHere, memos);
        seed.UnionWith(CollectSummarySeed(
            algorithm.Output,
            currentPropertySummaries,
            ownedHere,
            memos,
            inTransparentContext: false));

        // A name the opens/output walk reported unresolved from a transparent layer (a capture
        // row, a call or dot-call argument bundle — walked with empty local maps, see the arms
        // below) or from a nested block (whose completed summary knows nothing of this level)
        // is a reference written in THIS algorithm's lexical context, so ownership-first
        // resolution consults this algorithm's own properties before the name may escape to
        // the enclosing level — exactly as each property base seed is expanded against the
        // same local fixed point. Without this step `G = { Q = p + 1  (Q) }` reported the bare
        // name `Q` upward: an enclosing level with no `Q` dropped it (a local-only `G` leaked
        // through `open`), and an enclosing sibling `Q` was wrongly consulted (a self-contained
        // `G` was hidden). The same expansion turns each name this level's own `open`
        // declarations may provide into a pending reference carrying those providers.
        var finalLevel = new LevelContext(algorithm, currentPropertySummaries, memos);
        // Absorbed completed parts that only require names this level owns are exactly what the
        // expansion below would qualify and the strip after it remove: they are dropped by
        // reference, never folded (FE-3 — K owners that each absorbed one shared L-name argument
        // bundle seed would otherwise each copy, qualify, and strip its L names).
        seed.DropOwnedAbsorbedParts(ownedHere, sharedMemo);
        seed = ExpandAtLevel(seed, finalLevel);
        seed.RemoveRequiredAncestorOwnedParameterNames(ownedHere, algorithm,
            ownerHasParameters: ownerParameterNames.Count > 0 || completedContext is not null && locallyOwnedNames.Count > 0, observations);

        // A loaded module (Q-31 H-P) is wired to the prelude wherever it is held, exactly like an
        // inline open block: what still escapes its own levels is a
        // lookup only the prelude answers, so nothing of the holder's chain can be required.
        if (algorithm.IsModuleRoot)
            seed = SettledAtPrelude(seed);

        // Navigating a member does not call its owner. Retain the exact declaration
        // that binds each parameter instead of reinterpreting its name at the consumer:
        // every member seed is already qualified with this algorithm's parameter names, because
        // each one is its own expansion at this level (ExpandAtLevel qualifies with the same
        // names, and a shared seed is such an expansion too). Qualifying again would be a no-op
        // that folds, and so copies, every seed a member holds by reference (FE-4a).

        // The member seeds a consumer navigates into (`Inner.X`, an opened `X`) are the
        // level's final local summaries, which are relative to this level's PARENT: they keep
        // this level's own parameters as requirements (an `X = p` inside `Lib(p)` requires
        // `p` — that is exactly what makes it local-only), so only the output seed strips them.
        // A level that declares no property has no member to navigate into: it shares the one empty
        // member map instead of retaining its own empty dictionary in the completed-summary memo.
        return new AlgorithmSummary(seed, currentPropertySummaries.Count == 0 ? AlgorithmSummary.NoMembers : currentPropertySummaries);
    }

    /// <summary>
    /// The level expansion — THE ownership-first step of the summary channel at one level:
    /// a bare name or a pending reference's head that is one of the level's own properties
    /// resolves here (a bare name to that property's summary, a member path by structural
    /// navigation from that property's value); anything else escapes to the enclosing level,
    /// and when this level declares <c>open</c> targets those become the escaping reference's
    /// next candidates (after the candidates of the levels inside it — the inner-first order
    /// <c>open</c> lookup consults them in). Resolved candidate seeds riding along are seeds
    /// relative to this level and are expanded like everything else.
    /// </summary>
    internal static SummarySeed ExpandAtLevel(SummarySeed baseSeed, LevelContext level)
    {
        return RunExpansion(ExpandFrame(baseSeed, level)).Seed!;
    }

    /// <summary>
    /// OOS-22: ONE suspended step of the level expansion — an expansion at a level
    /// (<see cref="ExpandAtLevelCore"/>), one escaping reference's candidates
    /// (<see cref="AddEscaping"/>). These steps re-enter one another once per link of
    /// an opened chain (settling <c>P1</c>'s charge at the owner expands it there, which settles
    /// <c>P2</c>'s, …), so they never recurse on the host stack: each is a heap frame whose body
    /// yields the nested frame it needs next, and <see cref="RunExpansion"/> resumes it with that
    /// frame's result exactly where the recursive form would have returned. The evaluation order, the
    /// active-path and active-head cuts, and the per-level expansion cache are the recursive form's.
    /// Host calls that remain inside a body (navigation charges, expansions through nested nodes,
    /// nested-region summaries) descend into strictly nested levels, so their depth is bounded by the
    /// source's nesting, never by the chain's length.
    /// </summary>
    private sealed class ExpansionFrame
    {
        public IEnumerator<ExpansionFrame> Body = null!;
        public SummarySeed? Seed;
    }

    /// <summary>
    /// Runs <paramref name="root"/> to completion over an explicit stack: a frame yielding a nested
    /// frame is suspended until that frame completes. An exception unwinds every suspended frame
    /// innermost first, so each one's active key and level cache are released exactly as the
    /// recursion's <c>finally</c> blocks released them; no partial result is stored on that path.
    /// </summary>
    private static ExpansionFrame RunExpansion(ExpansionFrame root)
    {
        var frames = new Stack<ExpansionFrame>();
        frames.Push(root);
        try
        {
            while (frames.TryPeek(out var frame))
            {
                if (frame.Body.MoveNext())
                    frames.Push(frame.Body.Current);
                else
                    frames.Pop();
            }
        }
        finally
        {
            while (frames.TryPop(out var suspended))
                suspended.Body.Dispose();
        }

        return root;
    }

    private static ExpansionFrame ExpandFrame(SummarySeed baseSeed, LevelContext level)
    {
        var frame = new ExpansionFrame();
        frame.Body = ExpandAtLevelCore(frame, baseSeed, level);
        return frame;
    }

    private static ExpansionFrame EscapingFrame(SummarySeed expanded, PendingReference pending, LevelContext level)
    {
        var frame = new ExpansionFrame();
        frame.Body = AddEscaping(expanded, pending, level);
        return frame;
    }

    /// <summary>One expansion at <paramref name="level"/>; its result is <paramref name="self"/>'s <see cref="ExpansionFrame.Seed"/>.</summary>
    private static IEnumerator<ExpansionFrame> ExpandAtLevelCore(ExpansionFrame self, SummarySeed baseSeed, LevelContext level)
    {
        var outermost = level.ExpandedSeeds is null;
        var completed = level.ExpandedSeeds ??= new(StringComparer.Ordinal);
        try
        {
            var cacheKey = baseSeed.ContentKeyFor(level.Memos.Observations);
            if (completed.TryGetValue(cacheKey, out var cached))
            {
                self.Seed = cached.Clone();
                yield break;
            }

            var cuts = level.Memos.SharedMemo.ExpansionCycleCuts;
            var expanded = new SummarySeed(
                requiredAncestorOwnedParameterNames: baseSeed.RequiredAncestorOwnedParameterNames,
                ownerQualifiedParameters: baseSeed.OwnerQualifiedParameters);

            foreach (var dependencyName in baseSeed.VisiblePropertyDependencyNames)
            {
                if (level.LocalPropertySummaries.TryGetValue(dependencyName, out var localSummary))
                {
                    expanded.UnionWith(localSummary);
                    continue;
                }

                yield return EscapingFrame(expanded, new PendingReference(dependencyName, [], []), level);
            }

            foreach (var pending in baseSeed.PendingReferences)
            {
                if (level.Memos.CompletedContext is { } context)
                {
                    level.Memos.SharedMemo.UseContext();
                    // The same Q1-proved local equation bridge used by SolveMemberSeeds applies
                    // when anchoring an external seed through this owner. Read the live map so
                    // expansion-cache dependency tracking and invalidation remain unchanged.
                    if (level.Memos.SharedMemo.SelectsLocalMember(pending, context)
                        && level.LocalPropertySummaries.TryGetValue(pending.Head, out var local))
                    {
                        expanded.AbsorbCompleted(local);
                        continue;
                    }
                    expanded.PendingReferences.Add(pending.At(context));
                }
                else expanded.PendingReferences.Add(pending);
            }

            expanded.QualifyParameters(level.Algorithm, level.ParameterNames, level.Memos.Observations);
            // A partial expansion depends on the active path. It must never be served elsewhere.
            if (cuts == level.Memos.SharedMemo.ExpansionCycleCuts)
                completed.TryAdd(cacheKey, expanded.Clone());
            self.Seed = expanded;
        }
        finally
        {
            if (outermost)
                level.ExpandedSeeds = null;
        }
    }

    /// <summary>Carries a requirement's context without settling a raw path or provider.</summary>
    private static IEnumerator<ExpansionFrame> AddEscaping(SummarySeed expanded, PendingReference pending, LevelContext level)
    {
        if (level.Memos.CompletedContext is { } context)
        {
            level.Memos.SharedMemo.UseContext();
            expanded.PendingReferences.Add(pending.At(context));
        }
        else if (pending.Members.Count == 0) expanded.VisiblePropertyDependencyNames.Add(pending.Head);
        else expanded.PendingReferences.Add(pending);
        yield break;
    }

    /// <summary>Stops lexical requirement escape at the prelude without evaluating a provider.</summary>
    internal static SummarySeed SettledAtPrelude(SummarySeed seed)
        => new(seed.RequiredAncestorOwnedParameterNames, ownerQualifiedParameters: seed.OwnerQualifiedParameters);

    /// <summary>
    /// The static member path of a dot chain — a lexical head followed by argumentless dot
    /// steps, the shape the evaluator navigates structurally (<c>ResolveDotReceiver</c>) — with
    /// the final edge's member included whether or not it carries arguments. A step spelled
    /// <c>string</c> is navigated like any step (Q-17 S-C): navigation charges a declared
    /// member <c>string</c>, and a receiver the navigation stops at (the member is absent: the
    /// edge is the intrinsic, which reads that receiver's VALUE) charges its output exactly as
    /// the bare target seed would. False for every other receiver shape (a parameter, a block,
    /// a capture, a call).
    /// </summary>
    private static bool TryGetStaticMemberPath(Expr.DotCall dotCall, out string head, out IReadOnlyList<string> members)
    {
        var reversed = new List<string> { dotCall.Name };
        var current = dotCall.Target.UnwrapGraceOperand();
        while (current is Expr.DotCall { Args: null } edge)
        {
            reversed.Add(edge.Name);
            current = edge.Target.UnwrapGraceOperand();
        }

        if (current is Expr.Resolve(var name))
        {
            reversed.Reverse();
            head = name;
            members = reversed;
            return true;
        }

        head = string.Empty;
        members = [];
        return false;
    }

    /// <summary>
    /// The opens walk of a level: a named target charges the navigated provider path
    /// (<c>open A</c> needs only A's identity; <c>open A.B</c> charges the
    /// requirements of the navigated member <c>B</c>), an inline-headed target charges
    /// nothing (its block is wired to the prelude), and
    /// any other (illegal, recovery) shape walks as an ordinary expression. An open target is
    /// not a call, so no lexical fallback is ever charged for it.
    /// </summary>
    private static SummarySeed CollectOpenTargetSeeds(
        IReadOnlyList<Expr> opens,
        IReadOnlyDictionary<string, SummarySeed> localPropertySummaries,
        IReadOnlySet<string> ownedHere,
        SummaryWalkMemos memos)
    {
        var seed = new SummarySeed();
        foreach (var target in opens)
        {
            switch (target.OpenTargetHead(out var steps))
            {
                case Expr.Resolve(var head):
                    if (steps.Count > 0)
                        seed.UnionWith(new SummarySeed(pendingReferences: [new PendingReference(head, steps, [], origin: memos.CompletedContext, openPath: memos.CompletedContext is not null)]));
                    break;

                // An inline provider is also an identity, never an evaluated output, and so is
                // a dotted path navigated from one: the block is wired to the prelude, so neither
                // it nor any member reached from it can require anything of the opener's chain.
                // Provider signature/form validity is checked independently.
                case Expr.AlgorithmExpr:
                    break;

                default:
                    seed.UnionWith(CollectSummarySeed(target, localPropertySummaries, ownedHere, memos, inTransparentContext: false));
                    break;
            }
        }

        return seed;
    }

    private static SummarySeed CollectSummarySeed(
        Algorithm.Conditional algorithm,
        IReadOnlySet<string> locallyOwnedNames,
        SummaryMemo sharedMemo,
        FrontEndTraversalObservations? observations,
        CompletedStructureContext? completedContext = null)
    {
        var ownedHere = CreateNameSet(locallyOwnedNames);
        var localSummaries = new Dictionary<string, SummarySeed>(StringComparer.Ordinal);
        var memos = new SummaryWalkMemos(sharedMemo, observations, completedContext);
        var seed = CollectOpenTargetSeeds(
            algorithm.Opens,
            localSummaries,
            ownedHere,
            memos);

        var contributed = new HashSet<BranchBodySummaryKey>();
        foreach (var branch in algorithm.Branches)
        {
            // Branch bodies deliberately bypass the node-keyed completed-summary memo: their
            // binder-name context varies per branch, so their summaries are NOT pure
            // functions of the body node (see SummaryMemo). They are pure functions of
            // (body, binder names), which the branch-body memo keys on — so a body shared by
            // several families under the same binders is summarized once (M4).
            var context = sharedMemo.BranchContexts.NamesOf(branch.Pattern);
            var binderNames = context.Names;
            var branchContext = completedContext is null ? null : ChildContext(completedContext, branch.Body, branch.Pattern,
                algorithm.Opens.Count == 0);
            var key = new BranchBodySummaryKey(branch.Body, context.Id, branchContext?.Key, branchContext?.Facts);
            // Union is idempotent. One family's repeated reach of the same region contributes
            // nothing new, so skip BEFORE cloning or merging its potentially wide summary.
            if (!contributed.Add(key))
                continue;
            var contribution = CollectBranchBodySummarySeed(branch, binderNames, key, sharedMemo, observations, branchContext);
            observations?.RecordBranchSummaryContribution(contribution.RequiredAncestorOwnedParameterNames.Count
                + contribution.VisiblePropertyDependencyNames.Count + contribution.PendingReferences.Count
                + contribution.OwnerQualifiedParameters.Count);
            seed.UnionWith(contribution);
        }

        // Host-built families can own opens. They are a static lookup level above
        // the branch bodies, just as at runtime: never charge a provider's output,
        // and carry its candidate members when branch references escape this level.
        return algorithm.Opens.Count == 0 ? seed
            : ExpandAtLevel(seed, new LevelContext(algorithm, localSummaries, memos));
    }

    /// <summary>
    /// Memo-shared branch-body summary for one (body, binder-name set) — see
    /// <see cref="SummaryMemo.CompletedBranchBodySummaries"/>. Records completed computations
    /// (memo misses) only, like <see cref="CollectSharedAlgorithmSummarySeed"/>.
    /// </summary>
    private static SummarySeed CollectBranchBodySummarySeed(
        CondBranch branch,
        IReadOnlySet<string> binderNames,
        BranchBodySummaryKey key,
        SummaryMemo sharedMemo,
        FrontEndTraversalObservations? observations,
        CompletedStructureContext? completedContext)
    {
        completedContext = sharedMemo.SummaryRegion(completedContext, branch.Body);
        if (completedContext is not null) key = key with { Scope = completedContext.Key, Facts = completedContext.Facts };
        var independentKey = key with { Scope = null, Facts = null };
        var independent = sharedMemo.IndependentBranchSummaries ??= new();
        var canShare = completedContext is not null
            && sharedMemo.BranchParametersAgree(branch.Body, binderNames, completedContext);
        if (canShare && independent.TryGetValue(independentKey, out var shared)) return shared.Clone();
        var completedSummaries = sharedMemo.CompletedBranchBodySummaries ??= new();
        if (completedSummaries.TryGetValue(key, out var stored))
        {
            if (completedContext is not null) sharedMemo.UseContext();
            return stored.Clone();
        }

        var uses = sharedMemo.ContextUses;
        if (completedContext is not null && !canShare) sharedMemo.UseContext();
        observations?.RecordDependencyBranchBodySummaryComputation();
        var seed = CollectSummarySeed(branch.Body, CreateNameSet(binderNames), sharedMemo, observations, completedContext);
        if (canShare && uses == sharedMemo.ContextUses) independent.Add(independentKey, seed.Clone());
        else completedSummaries[key] = seed.Clone();
        return seed;
    }

    private static SummarySeed CollectSummarySeed(
        IReadOnlyList<Expr> expressions,
        IReadOnlyDictionary<string, SummarySeed> localPropertySummaries,
        IReadOnlySet<string> ownedHere,
        SummaryWalkMemos memos,
        bool inTransparentContext)
    {
        var seed = new SummarySeed();
        foreach (var expression in expressions)
            seed.UnionWith(CollectSummarySeed(expression, localPropertySummaries, ownedHere, memos, inTransparentContext));

        return seed;
    }

    private static SummarySeed CollectSummarySeed(
        Expr expr,
        IReadOnlyDictionary<string, SummarySeed> localPropertySummaries,
        IReadOnlySet<string> ownedHere,
        SummaryWalkMemos memos,
        bool inTransparentContext)
    {
        // DAG-safety: a shared node reference is summarized once per (region, context
        // flavor); every reach receives its own mutable CLONE of the pristine stored seed
        // (see SummaryWalkMemos), which is exactly what re-walking the duplicated tree
        // would contribute. The inTransparentContext flag travels in lock-step with the
        // empty summaries/owned-here maps the transparent arms pass. Childless leaves
        // build their seed in place.
        if (!AstTraversalDagSafety.HasTraversableExprChildren(expr))
            return CollectSummarySeedCore(expr, localPropertySummaries, ownedHere, memos, inTransparentContext);

        var seedMap = inTransparentContext
            ? memos.CompletedContext is null
                ? memos.SharedMemo.TransparentSeeds ??= new(ReferenceEqualityComparer.Instance)
                : memos.TransparentSeeds ??= new(ReferenceEqualityComparer.Instance)
            : memos.PrimarySeeds ??= new(ReferenceEqualityComparer.Instance);
        if (seedMap.TryGetValue(expr, out var stored))
            return stored.Clone();

        memos.Observations?.RecordDependencySeedExpansion();
        var seed = CollectSummarySeedCore(expr, localPropertySummaries, ownedHere, memos, inTransparentContext);
        seedMap[expr] = seed.Clone();
        return seed;
    }

    private static SummarySeed CollectSummarySeedCore(
        Expr expr,
        IReadOnlyDictionary<string, SummarySeed> localPropertySummaries,
        IReadOnlySet<string> ownedHere,
        SummaryWalkMemos memos,
        bool inTransparentContext)
    {
        SummarySeed Seed(Expr child)
            => CollectSummarySeed(child, localPropertySummaries, ownedHere, memos, inTransparentContext);

        return expr switch
        {
            Expr.Param(var name) => ownedHere.Contains(name)
                ? new SummarySeed()
                : new SummarySeed(requiredAncestorOwnedParameterNames: [name]),

            Expr.Resolve(var name) => localPropertySummaries.TryGetValue(name, out var localPropertySummary)
                ? localPropertySummary.Clone()
                : new SummarySeed(visiblePropertyDependencyNames: [name]),

            Expr.Grace(var inner, _) => Seed(inner),
            Expr.Binary(_, var left, var right) => Seed(left).Absorb(Seed(right)),
            Expr.Comparison(var first, var links) => links.Aggregate(Seed(first), (seed, link) => seed.Absorb(Seed(link.Operand))),
            Expr.Unary(_, var operand) => Seed(operand),
            // Selector slots are written in the ENCLOSING context, like list elements.
            Expr.Index(var target, var selectors) => Seed(target).Absorb(CollectSummarySeed(
                selectors, localPropertySummaries, ownedHere, memos, inTransparentContext)),
            Expr.SequenceSpread(var operand) => Seed(operand),
            Expr.SequenceConstruct(var left, var right) => Seed(left).Absorb(Seed(right)),
            Expr.ListLiteral(var listItems) => CollectSummarySeed(
                listItems, localPropertySummaries, ownedHere, memos, inTransparentContext),

            // Holes are expressions of the enclosing algorithm, like list elements (VAL-12).
            Expr.InterpolatedString(_, var interpolationLinks)
                => interpolationLinks.Aggregate(new SummarySeed(), (seed, link) => seed.Absorb(Seed(link.Hole))),

            Expr.AlgorithmExpr(var algorithm) => CollectSharedAlgorithmSummarySeed(algorithm, memos),

            // A capture owns no names: its rows walk with an empty
            // owned-here set and an empty local-summary map — exactly what
            // the pre-split transparent wrapper algorithm's output walk did
            // (the same attribution as call-argument bundles). The names it
            // reports unresolved are resolved against the enclosing
            // algorithm's own property summaries at the algorithm level
            // (CollectSummarySeed(Algorithm.User)), never left to escape.
            Expr.Capture(var captureBody) => CollectTransparentBundleSummarySeed(captureBody, memos),

            // An argument bundle owns no names: slots walk with an empty
            // owned-here set and an empty local-summary map — the same
            // attribution as capture rows (and as the pre-Track-B empty
            // transparent args wrapper). Its seed is a pure function of the
            // bundle, completed once per region and absorbed by reference when
            // large: a synthesized bundle shared by K call edges (FE-2) is
            // summarized once, not once per edge.
            Expr.Call(var function, var args) => Seed(function).AbsorbCompleted(CompletedArgumentBundleSeed(args, memos)),

            Expr.DotCall dotCall => CollectDotCallSummarySeed(
                dotCall, localPropertySummaries, ownedHere, memos, inTransparentContext),

            // Intentional leaves with no name occurrences: literals, the empty
            // sequence, and native-call bodies (whose argument names are
            // parameter references by construction).
            Expr.Num or Expr.StringLiteral or Expr.BoolLiteral or Expr.EmptySequence or Expr.NativeCall => new SummarySeed(),
        };
    }

    /// <summary>
    /// Seed of a scope-less bundle (capture rows, argument slots): the rows walk with an
    /// empty owned-here set and an empty local-summary map in the transparent context.
    /// </summary>
    private static SummarySeed CollectTransparentBundleSummarySeed(OutputBundle bundle, SummaryWalkMemos memos)
    {
        var seed = CollectSummarySeed(
            bundle.Head,
            new Dictionary<string, SummarySeed>(StringComparer.Ordinal),
            CreateNameSet(),
            memos,
            inTransparentContext: true);
        if (bundle.Tail is { } tail)
            seed.AbsorbCompleted(CompletedArgumentBundleSeed(tail, memos));
        return seed;
    }

    /// <summary>
    /// The COMPLETED seed of a call or dot-call argument bundle, computed once per bundle per
    /// region (the transparent walk's context is constant, so the seed is a pure function of the
    /// bundle) and never mutated afterwards — callers take it with
    /// <see cref="SummarySeed.AbsorbCompleted"/>. Implicit lifting shares one synthesized bundle
    /// between every lifted reference to a callee in a resolver region (FE-2).
    /// </summary>
    private static SummarySeed CompletedArgumentBundleSeed(OutputBundle bundle, SummaryWalkMemos memos)
    {
        var independent = memos.SharedMemo.IndependentArgumentBundles ??= new(ReferenceEqualityComparer.Instance);
        if (memos.CompletedContext is not null && independent.TryGetValue(bundle, out var shared)) return shared;
        var bundleSeeds = memos.CompletedContext is null
            ? memos.SharedMemo.ArgumentBundleSeeds ??= new(ReferenceEqualityComparer.Instance)
            : memos.ArgumentBundleSeeds ??= new(ReferenceEqualityComparer.Instance);
        if (!bundleSeeds.TryGetValue(bundle, out var seed))
        {
            var uses = memos.SharedMemo.ContextUses;
            memos.Observations?.RecordDependencyArgumentBundleSummary();
            seed = CollectTransparentBundleSummarySeed(bundle, memos);
            if (memos.CompletedContext is not null && uses == memos.SharedMemo.ContextUses)
                independent.Add(bundle, seed);
            else bundleSeeds.Add(bundle, seed);
        }
        else if (memos.CompletedContext is not null) memos.SharedMemo.UseContext();

        return seed;
    }

    /// <summary>
    /// The DotCall arm of <see cref="CollectSummarySeedCore"/>. A static member path
    /// (<c>Inner.X</c>, <c>Lib.Sub.Q</c>, <c>Lib.F(1)</c>) is charged by NAVIGATION at the
    /// level that resolves its head: every member the evaluator would navigate to charges
    /// its own requirements — so a container reading a captured member through
    /// <c>Inner.X</c> is itself local-only — and a receiver the walk stops at (the member
    /// is absent: the edge falls back) charges its output exactly as the bare target seed
    /// did. A receiver of any other shape (a parameter, a block, a capture, a call, the
    /// <c>string</c> intrinsic) is a value and keeps charging its own seed.
    /// <para>The stored lexical-fallback identity is an ordinary elaborated name expression
    /// (Resolve/Param) and participates in dependency analysis EXACTLY like a written
    /// callee name — through this same walk with the enclosing attribution — whenever the
    /// fallback MAY be selected at runtime (<see cref="AstHelpers.LexicalFallbackMayBeSelected"/>:
    /// the detector's stamped scope-aware verdict, or the raw shape classification on an
    /// unstamped edge). A receiver that declares the member never selects the fallback, so
    /// a Param fallback hidden behind a structural winner charges nothing and the property
    /// keeps its exported structural/open access; a receiver known to lack it — a sibling
    /// property whose value is a list, a call result, a literal — always does, so
    /// <c>Big = Data.f</c> with <c>f</c> an enclosing parameter is local-only exactly like
    /// the direct call <c>f(Data)</c>. Charging only CERTAIN selections left such a
    /// property exported although its value depends on the parameter: structural
    /// navigation could then read a dynamic binding through it, and the run-wide
    /// zero-argument property cache of an exported binding would have served one
    /// activation's value to another (SEMANTIC-ALIGNMENT, F3). The sibling
    /// evaluation-order channel (<see cref="CollectSiblingDependencyIndices"/>) deliberately
    /// takes no fallback contribution: the fallback is a CALLED name, and called siblings
    /// are not order dependencies there (the same rule as Call function position).</para>
    /// </summary>
    private static SummarySeed CollectDotCallSummarySeed(
        Expr.DotCall dotCall,
        IReadOnlyDictionary<string, SummarySeed> localPropertySummaries,
        IReadOnlySet<string> ownedHere,
        SummaryWalkMemos memos,
        bool inTransparentContext)
    {
        var seed = TryGetStaticMemberPath(dotCall, out var pathHead, out var pathMembers)
            ? new SummarySeed(pendingReferences: [new PendingReference(pathHead, pathMembers, [])])
            : CollectSummarySeed(dotCall.Target, localPropertySummaries, ownedHere, memos, inTransparentContext);

        if (dotCall.LexicalFallbackMayBeSelected())
        {
            seed.UnionWith(CollectSummarySeed(
                dotCall.EffectiveLexicalFallback,
                localPropertySummaries,
                ownedHere,
                memos,
                inTransparentContext));
        }

        if (dotCall.Args is { } argsOpt)
            seed.AbsorbCompleted(CompletedArgumentBundleSeed(argsOpt, memos));

        return seed;
    }

    /// <summary>
    /// FE-4a: the LEAST FIXED POINT of one algorithm's member-seed equations — member <c>i</c>'s seed is
    /// its base seed expanded at the level (<see cref="ExpandAtLevel"/>) against the current member
    /// seeds. Every expansion is monotone in those seeds (it unites them; which references escape and
    /// which providers settle them is structural), so any fair iteration from the empty seeds reaches
    /// the least fixed point the former round-by-round iteration reached. This one is dependency-driven:
    /// every equation is evaluated once and later only when a member seed it read has changed, so a
    /// chain of K members costs O(K) evaluations instead of K rounds of all K. The map is keyed by
    /// NAME and a name's equation is its LAST declaration's, exactly as the former last-write-wins map.
    ///
    /// <para>Evaluations SHARE seeds instead of copying them. A base seed that carries no path and only
    /// names local members (besides its own requirements) expands to exactly its own requirements,
    /// qualified here, united with those members' seeds — already expanded and qualified at this level.
    /// Content-empty member seeds contribute nothing; when the rest are ONE seed, the member IS that
    /// seed (no own requirements: K members aliasing one W-wide member hold one seed) or holds it BY
    /// REFERENCE beneath its own qualified delta (a member adding a few inputs to a shared W-wide member
    /// costs its delta). Base seeds of equal content expand to equal content while the member seeds
    /// they read stand, so any other expansion is reused, validated by those reads, for every member
    /// whose base seed has that content (K members reading one opened or navigated member expand it
    /// once). A member seed is never mutated after it enters the map (every one is its own expansion at
    /// this level, so it is already qualified), and every consumer clones a member seed before
    /// accumulating, so sharing is unobservable. Change detection compares structure first (own sets
    /// and the seeds held by reference) and folds only when that cannot decide.</para>
    /// </summary>
    private static void SolveMemberSeeds(
        Algorithm algorithm,
        SummarySeed[] baseSeeds,
        Dictionary<string, SummarySeed> seeds,
        SummaryWalkMemos memos)
    {
        var properties = algorithm.Properties;
        var recorded = new RecordingMemberSeeds(seeds);
        var level = new LevelContext(algorithm, recorded, memos);
        var equationOf = new Dictionary<string, int>(StringComparer.Ordinal);
        for (var i = 0; i < properties.Count; i++)
            equationOf[properties[i].Name] = i;

        // Equivalent completed consumers can have distinct origin keys but select the same local
        // declaration. Bridge only that proven selection to the existing live dependency equation;
        // never substitute a completed summary snapshot for a fixed-point read.
        if (memos.CompletedContext is { } completed)
            for (var i = 0; i < baseSeeds.Length; i++)
            {
                var seed = baseSeeds[i];
                if (seed.PendingReferences.Count > 0)
                {
                    var references = seed.PendingReferences.Select(memos.SharedMemo.SelectedReference).ToArray();
                    if (!references.SequenceEqual(seed.PendingReferences))
                    {
                        seed = seed.Clone();
                        seed.PendingReferences.Clear();
                        seed.PendingReferences.UnionWith(references);
                        baseSeeds[i] = seed;
                    }
                }
                SummarySeed? bridged = null;
                HashSet<PendingReference>? selected = null;
                foreach (var reference in seed.PendingReferences)
                {
                    if (!equationOf.ContainsKey(reference.Head) || !memos.SharedMemo.SelectsLocalMember(reference, completed)) continue;
                    bridged ??= seed.Clone();
                    (selected ??= []).Add(reference);
                    bridged.VisiblePropertyDependencyNames.Add(reference.Head);
                }
                if (bridged is not null)
                {
                    bridged.PendingReferences.Clear();
                    bridged.PendingReferences.UnionWith(seed.PendingReferences.Where(reference => !selected!.Contains(reference)));
                    baseSeeds[i] = bridged;
                }
            }

        // Statically read members: the local names a base seed reads directly or heads a path with.
        IEnumerable<int> StaticReads(int index)
        {
            var baseSeed = baseSeeds[index];
            foreach (var name in baseSeed.VisiblePropertyDependencyNames)
                if (equationOf.TryGetValue(name, out var read))
                    yield return read;
            foreach (var pending in baseSeed.PendingReferences)
                if (equationOf.TryGetValue(pending.Head, out var read))
                    yield return read;
        }

        // Evaluation units, dependency first. A strongly connected component whose every member has the
        // SHARE shape (TryShareMemberSeed) is a system of pure unions over exactly its static edges, so
        // its least fixed point gives every member the SAME seed: the members' own requirements,
        // qualified here, united with the seeds the component reads from outside. It is solved as ONE
        // unit (its first member stands for it) instead of propagating each member's requirements
        // around the cycle member by member.
        var components = DependencyFirstOrder.Components(properties.Count, i => equationOf[properties[i].Name] == i, StaticReads);
        var componentOf = new int[properties.Count];
        Array.Fill(componentOf, -1);
        var queue = new Queue<int>();
        var queued = new bool[properties.Count];
        for (var c = 0; c < components.Count; c++)
        {
            var component = components[c];
            if (component.Count > 1 && component.TrueForAll(member => HasShareShape(baseSeeds[member], equationOf)))
            {
                foreach (var member in component)
                    componentOf[member] = c;
                queue.Enqueue(component[0]);
                queued[component[0]] = true;
                continue;
            }

            foreach (var member in component)
            {
                queue.Enqueue(member);
                queued[member] = true;
            }
        }

        var readers = new Dictionary<string, HashSet<int>>(StringComparer.Ordinal);
        var contentKeys = new string?[properties.Count];
        Dictionary<string, (SummarySeed Result, (string Name, SummarySeed Read)[] Reads)>? expansions = null;
        while (queue.TryDequeue(out var index))
        {
            queued[index] = false;
            memos.Observations?.RecordSummaryMemberEvaluation();
            recorded.Reads.Clear();
            var component = componentOf[index];
            var next = component < 0 ? EvaluateMemberSeed(index) : EvaluateComponent(components[component], component);
            foreach (var readName in recorded.Reads)
            {
                if (!readers.TryGetValue(readName, out var nameReaders))
                    readers.Add(readName, nameReaders = []);
                nameReaders.Add(index);
            }

            // The members of one unit share their previous seed after the unit's first evaluation,
            // so one comparison decides them all.
            SummarySeed? comparedPrevious = null;
            var comparedSame = false;
            foreach (var member in component < 0 ? [index] : components[component])
            {
                var name = properties[member].Name;
                var previous = seeds[name];
                if (!ReferenceEquals(previous, comparedPrevious))
                {
                    comparedPrevious = previous;
                    comparedSame = SameContent(next, previous);
                }

                if (comparedSame)
                    continue;

                seeds[name] = next;
                if (!readers.TryGetValue(name, out var dependents))
                    continue;
                foreach (var dependent in dependents)
                {
                    memos.Observations?.RecordSummaryMemberReaderNotification();
                    if (!queued[dependent])
                    {
                        queued[dependent] = true;
                        queue.Enqueue(dependent);
                    }
                }
            }
        }

        // One share-shaped component's seed: its members' own requirements qualified here, united with
        // the non-empty seeds it reads from outside itself (held by reference when large).
        SummarySeed EvaluateComponent(List<int> members, int component)
        {
            var value = new SummarySeed(
                members.SelectMany(member => baseSeeds[member].RequiredAncestorOwnedParameterNames),
                ownerQualifiedParameters: members.SelectMany(member => baseSeeds[member].OwnerQualifiedParameters));
            value.QualifyParameters(level.Algorithm, level.ParameterNames, memos.Observations);
            foreach (var member in members)
            {
                foreach (var name in baseSeeds[member].VisiblePropertyDependencyNames)
                {
                    if (componentOf[equationOf[name]] == component)
                        continue;
                    recorded.Reads.Add(name);
                    if (!seeds[name].IsEmptyWithoutFolding())
                        value.AbsorbCompleted(seeds[name]);
                }
            }

            return value;
        }

        SummarySeed EvaluateMemberSeed(int index)
        {
            var baseSeed = baseSeeds[index];
            if (TryShareMemberSeed(baseSeed, recorded, level) is { } shared)
                return shared;

            var key = contentKeys[index] ??= baseSeed.ContentKeyFor(memos.Observations);
            expansions ??= new(StringComparer.Ordinal);
            if (expansions.TryGetValue(key, out var expansion)
                && expansion.Reads.All(read => ReferenceEquals(seeds[read.Name], read.Read)))
            {
                foreach (var (readName, _) in expansion.Reads)
                    recorded.Reads.Add(readName);
                return expansion.Result;
            }

            memos.Observations?.RecordSummaryMemberExpansion();
            var expanded = ExpandAtLevel(baseSeed, level);
            expansions[key] = (expanded, [.. recorded.Reads.Select(readName => (readName, seeds[readName]))]);
            return expanded;
        }
    }

    // The SHARE shape: a base seed with no path whose visible names are all members of the level. Its
    // expansion is exactly its own requirements, qualified at the level, united with those members' seeds.
    private static bool HasShareShape(SummarySeed baseSeed, Dictionary<string, int> members)
        => baseSeed.PendingReferences.Count == 0
            && baseSeed.VisiblePropertyDependencyNames.Count != 0
            && baseSeed.VisiblePropertyDependencyNames.All(members.ContainsKey);

    // The expansion of a share-shaped base seed, built by SHARING the members' seeds it reads (see
    // SolveMemberSeeds): content-empty member seeds contribute nothing, and the rest must be ONE seed.
    // Null when the base seed does not have that shape or reads several distinct non-empty seeds.
    private static SummarySeed? TryShareMemberSeed(SummarySeed baseSeed, RecordingMemberSeeds seeds, LevelContext level)
    {
        if (baseSeed.PendingReferences.Count != 0 || baseSeed.VisiblePropertyDependencyNames.Count == 0)
            return null;

        SummarySeed? shared = null;
        SummarySeed? empty = null;
        foreach (var name in baseSeed.VisiblePropertyDependencyNames)
        {
            if (!seeds.Seeds.TryGetValue(name, out var member))
                return null;
            if (member.IsEmptyWithoutFolding())
            {
                empty ??= member;
                continue;
            }

            if (shared is not null && !ReferenceEquals(shared, member))
                return null;
            shared = member;
        }

        foreach (var name in baseSeed.VisiblePropertyDependencyNames)
            seeds.Reads.Add(name);
        if (baseSeed.RequiredAncestorOwnedParameterNames.Count == 0 && baseSeed.OwnerQualifiedParameters.Count == 0)
            return shared ?? empty;

        // Own requirements, qualified here exactly as a full expansion qualifies them (the shared
        // member is already qualified at this level, and qualification distributes over union).
        var delta = new SummarySeed(
            baseSeed.RequiredAncestorOwnedParameterNames,
            ownerQualifiedParameters: baseSeed.OwnerQualifiedParameters);
        delta.QualifyParameters(level.Algorithm, level.ParameterNames, level.Memos.Observations);
        return shared is null ? delta : delta.AbsorbCompleted(shared);
    }

    // Exact content equality of a member's new and previous seed, without folding when structure decides.
    private static bool SameContent(SummarySeed next, SummarySeed previous)
    {
        if (ReferenceEquals(next, previous))
            return true;
        if (previous.IsEmptyWithoutFolding())
            return next.IsEmptyWithoutFolding();
        return next.StructurallyEquals(previous) || next.SetEquals(previous);
    }

    /// <summary>
    /// The member-seed map of a level whose fixed point is being solved, recording which members'
    /// seeds an expansion READ (a <see cref="TryGetValue"/> hit): the solver re-evaluates a member
    /// exactly when a seed it read has changed. Presence tests (<see cref="ContainsKey"/>) are
    /// structural — which members a level declares never changes — and record nothing.
    /// </summary>
    private sealed class RecordingMemberSeeds(Dictionary<string, SummarySeed> seeds) : IReadOnlyDictionary<string, SummarySeed>
    {
        public Dictionary<string, SummarySeed> Seeds { get; } = seeds;

        public HashSet<string> Reads { get; } = new(StringComparer.Ordinal);

        public bool TryGetValue(string key, [System.Diagnostics.CodeAnalysis.MaybeNullWhen(false)] out SummarySeed value)
        {
            if (!Seeds.TryGetValue(key, out value))
                return false;
            Reads.Add(key);
            return true;
        }

        public SummarySeed this[string key]
        {
            get
            {
                var value = Seeds[key];
                Reads.Add(key);
                return value;
            }
        }

        public bool ContainsKey(string key) => Seeds.ContainsKey(key);

        public IEnumerable<string> Keys => Seeds.Keys;

        public IEnumerable<SummarySeed> Values => throw new NotSupportedException("A member-seed view is read by name.");

        public int Count => Seeds.Count;

        public IEnumerator<KeyValuePair<string, SummarySeed>> GetEnumerator()
            => throw new NotSupportedException("A member-seed view is read by name.");

        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();
    }

    /// <summary>
    /// The constant inputs of ONE property's sibling-dependency collection: the sibling name
    /// set, the level's prelude-shadow predicate, the name→index map, the accumulating index
    /// set, the property's own index, and the walk memo.
    /// </summary>
    private sealed record SiblingWalkContext(
        HashSet<string> SiblingNames,
        IReadOnlyDictionary<string, int> PropertyNameToIndex,
        HashSet<int> DependencyIndices,
        int PropertyIndex,
        SiblingWalkMemo Memo,
        SiblingOrderLookup? Lookup)
    {
        /// <summary>The siblings this property MAY read through what the channel cannot classify (see <see cref="PropertyDependencyNode"/>).</summary>
        public HashSet<int> SoftDependencyIndices { get; init; } = [];
    }

    /// <summary>
    /// The names bound by the bodies between a property's value and the node being walked
    /// (the value's own properties included: its output rows resolve inside its own scope). A
    /// body's own property names shadow same-named siblings for everything inside it —
    /// ownership-first lookup reaches the enclosing level's siblings before any open — so a
    /// shadowed reference is no processing-order dependency; binders and parameters are
    /// already <see cref="Expr.Param"/>s and never match a sibling name. The scope composes
    /// the level's prelude-shadow predicate with those names, so a nested <c>abs</c> property
    /// shadows the alias inside that body exactly as a sibling <c>abs</c> does at the level.
    /// <see cref="Key"/> is the content identity the walk memo splits on: a canonical name set of
    /// the walk's <see cref="NameSetInterner"/> (FE-1), so entering a body EXTENDS the outer set by
    /// the body's own names — never re-copying and re-sorting every name the enclosing bodies
    /// already shadow — and equal shadow contents share one key whatever bodies built them.
    /// </summary>
    private sealed class ShadowScope
    {
        private readonly NameSetInterner _interner;
        private readonly CanonicalNameSet _names;
        private readonly Func<string, bool> _levelShadowed;

        private ShadowScope(NameSetInterner interner, CanonicalNameSet names, Func<string, bool> levelShadowed)
        {
            _interner = interner;
            _names = names;
            _levelShadowed = levelShadowed;
            // The names are cumulative (every enclosing body's included), so ONE predicate over
            // them plus the level's own reproduces the former chain of per-body closures.
            PreludeNameShadowed = name => interner.Contains(names, name) || levelShadowed(name);
        }

        public static ShadowScope Level(NameSetInterner interner, Func<string, bool> preludeNameShadowed)
            => new(interner, NameSetInterner.Empty, preludeNameShadowed);

        public int Key => _names.Id;

        public Func<string, bool> PreludeNameShadowed { get; }

        public bool Shadows(string name) => _interner.Contains(_names, name);

        // A name no identifier spells: present when a body between the level and the walk has opens of its own.
        private const string NestedOpensMark = "\0open";

        /// <summary>
        /// Whether a body between the level and the walk has opens of its own: a name the owner walk leaves to the opens
        /// may then reach that body's provider before the level's.
        /// </summary>
        public bool HasNestedOpens => _interner.Contains(_names, NestedOpensMark);

        public ShadowScope Enter(Algorithm body, SiblingWalkMemo memo)
        {
            if (body.Properties.Count == 0 && body.Opens.Count == 0)
                return this;

            if (memo.EnteredShadows.TryGetValue((Key, body), out var entered))
                return entered;
            if (!memo.OwnShadowNames.TryGetValue(body, out var own))
            {
                var declared = body.Properties.Select(static property => property.Name);
                own = _interner.With(NameSetInterner.Empty, body.Opens.Count > 0 ? declared.Append(NestedOpensMark) : declared);
                memo.OwnShadowNames.Add(body, own);
            }
            var names = _interner.Union(_names, own);
            entered = names.Equals(_names) ? this : new ShadowScope(_interner, names, _levelShadowed);
            memo.EnteredShadows.Add((Key, body), entered);
            return entered;
        }
    }

    /// <summary>
    /// Collects the sibling dependencies of ONE property value: every sibling reference anywhere in
    /// the value's subtree whose processed signature the resolver READS — a VALUE-role reference
    /// (THE role classifier, <see cref="FormulaLiftingRoles"/>, the one the rewrite uses), the head of
    /// a value-role structural dotted callee, and the sibling heading the level's own open provider of
    /// a value-role opened name — that no nested body shadows: its output rows, its nested property
    /// values, block literals and capture rows in expression position, and every branch body of a
    /// conditional family, because the resolver rewrites all of those while processing the property.
    /// Complete edges are what make the topological order process a sibling before every consumer,
    /// whatever the declaration order, so no consumer's rewrite depends on where it was written; a
    /// read this channel can only anticipate (a body's own <c>open</c> of a sibling, a bare sibling
    /// argument of a callee it cannot classify) is a soft preference, and a read that still reaches a
    /// pending sibling is processed on demand by the resolver. Memoized per (node, shadow context,
    /// role): a shared subtree is walked once per context, never once per path.
    /// </summary>
    private static void CollectAlgorithmSiblingDependencyIndices(
        Algorithm value,
        SiblingWalkContext context,
        ShadowScope shadow)
    {
        switch (value)
        {
            // A loaded module (Q-31 H-P) is a source unit rooted at the prelude: nothing in it
            // reads the level that holds it, so it contributes no processing-order dependency.
            case Algorithm.User { IsModuleElaborated: true }:
            case Algorithm.Alias { IsModuleElaborated: true }:
                break;

            // A callable alias (an already elaborated body: its one row is its target reference)
            // reads its target exactly as a body whose one row names it.
            case Algorithm.User or Algorithm.Alias:
            {
                var inner = shadow.Enter(value, context.Memo);
                if (!context.Memo.Algorithms(inner.Key).Add(value))
                    return;

                // A body's own `open` of a sibling (its head resolves through the body's direct
                // chain): the resolver reads an opened member's PROCESSED signature through it, and
                // this channel cannot tell which names reach that provider — a soft preference.
                foreach (var open in value.Opens)
                {
                    if (open.OpenTargetHead() is Expr.Resolve(var head) && !inner.Shadows(head))
                        AddSoftSiblingDependency(context, head);
                }

                foreach (var row in value.Output)
                    CollectSiblingDependencyIndices(row, context, inner, LiftingRole.Value);

                foreach (var property in value.Properties)
                    CollectAlgorithmSiblingDependencyIndices(property.Value, context, inner);
                break;
            }

            case Algorithm.Conditional conditional:
            {
                if (!context.Memo.Algorithms(shadow.Key).Add(conditional))
                    return;

                // Family-owned opens are open targets, which the resolver never reads through
                // the signature map; binders are Params. Each branch body is a body of its own,
                // resolved inside the family's scope.
                foreach (var branch in conditional.Branches)
                    CollectAlgorithmSiblingDependencyIndices(branch.Body, context, shadow);
                break;
            }

            case Algorithm.Builtin:
                break;

            default:
                throw new InvalidOperationException(
                    $"Unhandled Algorithm variant in {nameof(PropertyDependencyGraphBuilder)}.{nameof(CollectAlgorithmSiblingDependencyIndices)}: {value.GetType().Name}.");
        }
    }

    private static void CollectSiblingDependencyIndices(
        Expr expr,
        SiblingWalkContext context,
        ShadowScope shadow,
        LiftingRole role)
    {
        // DAG-safety: contributions are index-set idempotent, so a completed node reference
        // reached again under the same shadow context and role is skipped (see
        // SiblingWalkMemo).
        if (!AstTraversalDagSafety.HasTraversableExprChildren(expr))
        {
            CollectSiblingDependencyIndicesCore(expr, context, shadow, role);
            return;
        }

        var visited = context.Memo.Visited(shadow.Key, role);
        if (visited.Contains(expr))
            return;

        context.Memo.Observations?.RecordDependencySiblingExpansion();
        CollectSiblingDependencyIndicesCore(expr, context, shadow, role);
        visited.Add(expr);
    }

    private static void CollectSiblingDependencyIndicesCore(
        Expr expr,
        SiblingWalkContext context,
        ShadowScope shadow,
        LiftingRole role)
    {
        switch (expr)
        {
            case Expr.Resolve(var name):
                if (role == LiftingRole.Value && !shadow.Shadows(name))
                {
                    if (context.SiblingNames.Contains(name))
                        AddSiblingDependency(context, context.PropertyNameToIndex.TryGetValue(name, out var dependencyIndex) ? dependencyIndex : null);
                    // A nested open may supply this name before the level's provider. This channel has no
                    // nested provider context; leave that signature read to the resolver's on-demand path,
                    // just as RefinedMiss does, rather than inventing a dependency on the outer provider.
                    else if (!shadow.HasNestedOpens && context.Lookup?.OpenedSiblingProvider(name) is { } providerIndex)
                        AddSiblingDependency(context, providerIndex);
                }
                break;

            case Expr.Call(var function, var callArgs):
            {
                CollectSiblingDependencyIndices(function, context, shadow, LiftingRole.Callable);
                var roles = FormulaLiftingRoles.ArgumentRoles(SiblingWalkCalleeKind(function, context, shadow), callArgs);
                var unclassified = IsUnclassifiedCallee(function, context, shadow);
                for (var i = 0; i < callArgs.Count; i++)
                {
                    if (unclassified && roles[i] == LiftingRole.Callable)
                        AddSoftSiblingReference(context, shadow, callArgs[i]);
                    CollectSiblingDependencyIndices(callArgs[i], context, shadow, roles[i]);
                }

                break;
            }

            case Expr.Binary(_, var left, var right):
                CollectSiblingDependencyIndices(left, context, shadow, LiftingRole.Value);
                CollectSiblingDependencyIndices(right, context, shadow, LiftingRole.Value);
                break;

            case Expr.Comparison(var first, var links):
                CollectSiblingDependencyIndices(first, context, shadow, LiftingRole.Value);
                foreach (var link in links)
                    CollectSiblingDependencyIndices(link.Operand, context, shadow, LiftingRole.Value);
                break;

            case Expr.Unary(_, var operand):
                CollectSiblingDependencyIndices(operand, context, shadow, LiftingRole.Value);
                break;

            case Expr.Index(var target, var selectors):
                // The receiver and every selector slot are VALUE uses; a selection has no callee.
                CollectSiblingDependencyIndices(target, context, shadow, LiftingRole.Value);
                foreach (var selector in selectors)
                    CollectSiblingDependencyIndices(selector, context, shadow, LiftingRole.Value);
                break;

            case Expr.SequenceSpread(var operand):
                CollectSiblingDependencyIndices(operand, context, shadow, LiftingRole.Value);
                break;

            case Expr.SequenceConstruct(var left, var right):
                CollectSiblingDependencyIndices(left, context, shadow, LiftingRole.Value);
                CollectSiblingDependencyIndices(right, context, shadow, LiftingRole.Value);
                break;

            case Expr.ListLiteral(var listItems):
                foreach (var item in listItems)
                    CollectSiblingDependencyIndices(item, context, shadow, LiftingRole.Value);
                break;

            case Expr.Capture(var captureBody):
                // A capture element is a value: the resolver lifts it.
                foreach (var row in captureBody)
                    CollectSiblingDependencyIndices(row, context, shadow, LiftingRole.Value);
                break;

            case Expr.InterpolatedString(_, var interpolationLinks):
                // An interpolation hole is a value: the resolver lifts it (VAL-12).
                foreach (var link in interpolationLinks)
                    CollectSiblingDependencyIndices(link.Hole, context, shadow, LiftingRole.Value);
                break;

            case Expr.DotCall dotCall:
            {
                var missSelection = dotCall.EffectiveMissSelection();
                CollectDotEdgeSiblingDependencies(dotCall, FormulaLiftingRoles.EdgeKind(dotCall, missSelection), context, shadow, role);

                // A miss detection leaves to the runtime receiver (MAY) that implicit-argument resolution refines (M4★),
                // read as resolution reads it (SiblingOrderLookup.RefinedMiss): where resolution's input decides that the
                // receiver certainly lacks the member, the edge reads what a certain miss reads, so those are dependencies;
                // where the receiver is an `.Algorithm` link body only its processing decides, resolution processes it
                // exactly where a certain miss would give a slot a VALUE role, so that body's sibling is one where this
                // channel's classification gives one (a slot it cannot classify the rewrite reads on demand). Nothing else
                // is read: a parameter's member, a runtime reference's, an unresolved name's.
                if (missSelection == LexicalFallbackSelection.Conditional
                    && !PathHeadShadowed(dotCall.Target, shadow)
                    && context.Lookup?.RefinedMiss?.Invoke(dotCall, shadow.HasNestedOpens) is { } refined)
                {
                    var certainMiss = FormulaLiftingRoles.EdgeKind(dotCall, LexicalFallbackSelection.Always);
                    if (refined.CertainMiss)
                        CollectDotEdgeSiblingDependencies(dotCall, certainMiss, context, shadow, role);
                    else if (refined.Link is { } link && CertainMissReadsAValue(dotCall, certainMiss, context, shadow))
                        AddSiblingDependency(context, link);
                }

                break;
            }

            case Expr.Grace(var inner, _):
                CollectSiblingDependencyIndices(inner, context, shadow, role);
                break;

            case Expr.AlgorithmExpr(var nested):
                // A block literal is a body of its own in every position: the resolver
                // rewrites it (and reads sibling signatures inside it) wherever it stands.
                CollectAlgorithmSiblingDependencyIndices(nested, context, shadow);
                break;

            // Intentional leaves: no sibling references.
            case Expr.Num:
            case Expr.Param:
            case Expr.StringLiteral:
            case Expr.BoolLiteral:
            case Expr.EmptySequence:
            case Expr.NativeCall:
                break;

            // Runtime exhaustiveness guard (statement-form collector, which the
            // closed Expr hierarchy cannot make compiler-exhaustive — see
            // AstWalker.VisitExpr): a new Expr variant must be classified above
            // rather than silently contributing no processing-order dependencies.
            default:
                throw new InvalidOperationException(
                    $"Unhandled Expr variant in {nameof(PropertyDependencyGraphBuilder)}.{nameof(CollectSiblingDependencyIndices)}: {expr.GetType().Name}. " +
                    "Classify the new variant explicitly as a collected case or an intentional leaf.");
        }
    }

    /// <summary>
    /// Whether a callee's KIND is beyond this channel's resolution power — a callee a nested body
    /// declares, one only an <c>open</c> provides, or a structural member — while the resolver
    /// knows it (and so may classify a whole argument as a value it reads). A parameter or a computed
    /// callee is dynamic to the resolver as well, so it is not unclassified.
    /// </summary>
    private static bool IsUnclassifiedCallee(Expr callee, SiblingWalkContext context, ShadowScope shadow)
        => callee.UnwrapGraceOperand() switch
        {
            Expr.Resolve { ElaboratedMathMember: not null } opened => shadow.Shadows(opened.Name),
            Expr.Resolve resolve => shadow.Shadows(resolve.Name)
                || SiblingWalkCalleeKind(resolve, context, shadow).Kind == LiftingCalleeKind.Dynamic,
            Expr.DotCall { Args: null } edge => !edge.TryGetRegistryProvenCanonicalMathFacts(shadow.PreludeNameShadowed, out _),
            _ => false,
        };

    /// <summary>
    /// A sibling reference in a slot of an unclassified callee, which the resolver may read as a value: a soft preference
    /// (see <see cref="PropertyDependencyNode"/>) — a bare unshadowed sibling name, or a structural member path that reads
    /// a sibling through the level's own owner (<c>Lib.A</c> inside Lib, the soft counterpart of a value-role path's
    /// dependency, <see cref="SiblingOrderLookup.OwnedMemberSibling"/>: identity never spelling).
    /// </summary>
    private static void AddSoftSiblingReference(SiblingWalkContext context, ShadowScope shadow, Expr slot)
    {
        switch (slot.UnwrapGraceOperand())
        {
            case Expr.Resolve(var name) when !shadow.Shadows(name):
                AddSoftSiblingDependency(context, name);
                break;
            case Expr.DotCall { Args: null } path
                when path.EffectiveMissSelection() == LexicalFallbackSelection.Never
                    && !PathHeadShadowed(path, shadow)
                    && context.Lookup?.OwnedMemberSibling?.Invoke(path) is { } index
                    && index != context.PropertyIndex:
                context.SoftDependencyIndices.Add(index);
                break;
        }
    }

    private static void AddSoftSiblingDependency(SiblingWalkContext context, string name)
    {
        if (context.SiblingNames.Contains(name)
            && context.PropertyNameToIndex.TryGetValue(name, out var index)
            && index != context.PropertyIndex)
        {
            context.SoftDependencyIndices.Add(index);
        }
    }

    private static void AddSiblingDependency(SiblingWalkContext context, int? dependencyIndex)
    {
        if (dependencyIndex is { } index && index != context.PropertyIndex)
            context.DependencyIndices.Add(index);
    }

    /// <summary>
    /// The dependencies of one dot edge dispatched as <paramref name="kind"/> (the DotCall arm of
    /// <see cref="CollectSiblingDependencyIndicesCore"/>): its receiver and arguments in the roles of that dispatch.
    /// </summary>
    private static void CollectDotEdgeSiblingDependencies(
        Expr.DotCall dotCall,
        DotEdgeKind kind,
        SiblingWalkContext context,
        ShadowScope shadow,
        LiftingRole role)
    {
        if (dotCall.Args is null && kind == DotEdgeKind.StructuralMember)
        {
            // A dotted callee: in a value role the resolver reads its member's PROCESSED
            // signature through its receiver, so a sibling receiver is a dependency — and so is
            // the member itself when the path selects a property of this level through the
            // level's own owner (`Lib.A` inside Lib: the sibling A, whatever its spelling); in a
            // callable role the receiver is only navigated.
            if (role == LiftingRole.Value
                && !PathHeadShadowed(dotCall, shadow)
                && context.Lookup?.OwnedMemberSibling?.Invoke(dotCall) is { } memberIndex)
            {
                AddSiblingDependency(context, memberIndex);
            }

            CollectSiblingDependencyIndices(dotCall.Target, context, shadow, role);
            return;
        }

        var callee = kind switch
        {
            DotEdgeKind.StructuralMember => SiblingWalkCalleeKind(dotCall with { Args = null }, context, shadow),
            DotEdgeKind.Fallback => SiblingWalkCalleeKind(dotCall.EffectiveLexicalFallback, context, shadow),
            _ => LiftingCallee.Dynamic,
        };
        var unclassified = kind switch
        {
            DotEdgeKind.StructuralMember => IsUnclassifiedCallee(dotCall with { Args = null }, context, shadow),
            DotEdgeKind.Fallback => IsUnclassifiedCallee(dotCall.EffectiveLexicalFallback, context, shadow),
            _ => false,
        };
        var receiverRole = FormulaLiftingRoles.ReceiverRole(kind, callee);
        var roles = dotCall.Args is not null ? FormulaLiftingRoles.DotArgumentRoles(dotCall, kind, callee) : null;
        if (unclassified && kind == DotEdgeKind.Fallback && receiverRole == LiftingRole.Callable)
            AddSoftSiblingReference(context, shadow, dotCall.Target);
        CollectSiblingDependencyIndices(dotCall.Target, context, shadow, receiverRole);
        if (dotCall.Args is { } args)
        {
            for (var i = 0; i < args.Count; i++)
            {
                if (unclassified && roles![i] == LiftingRole.Callable)
                    AddSoftSiblingReference(context, shadow, args[i]);
                CollectSiblingDependencyIndices(args[i], context, shadow, roles![i]);
            }
        }
    }

    /// <summary>
    /// Whether the dispatch <paramref name="kind"/> of <paramref name="dotCall"/> — a certain miss's — gives its receiver or
    /// an argument a VALUE role as this channel classifies its callee: where implicit-argument resolution's own
    /// classification gives one too, so it reads the receiver to refine the edge.
    /// </summary>
    private static bool CertainMissReadsAValue(Expr.DotCall dotCall, DotEdgeKind kind, SiblingWalkContext context, ShadowScope shadow)
    {
        var callee = kind == DotEdgeKind.Fallback
            ? SiblingWalkCalleeKind(dotCall.EffectiveLexicalFallback, context, shadow)
            : LiftingCallee.Dynamic;
        return FormulaLiftingRoles.ReceiverRole(kind, callee) == LiftingRole.Value
            || (dotCall.Args is not null && FormulaLiftingRoles.DotArgumentRoles(dotCall, kind, callee).Contains(LiftingRole.Value));
    }

    /// <summary>Whether a body between the property value and <paramref name="path"/> declares the head name of the member path it is.</summary>
    private static bool PathHeadShadowed(Expr path, ShadowScope shadow)
    {
        var head = path.UnwrapGraceOperand();
        while (head is Expr.DotCall { Args: null } edge)
            head = edge.Target.UnwrapGraceOperand();
        return head is Expr.Resolve(var name) && shadow.Shadows(name);
    }

    /// <summary>
    /// The kind of a callee as this channel resolves it: a name no nested body shadows through the
    /// level's owner walk (<see cref="SiblingOrderLookup.CalleeKindOf"/>), an opened Math member by
    /// parameter detection's stamp, and the canonical <c>Math.X</c> shape; anything else — a callee a
    /// nested body declares, a member only an open provides — is <see cref="LiftingCalleeKind.Dynamic"/>
    /// here, which classifies no slot as a value, so this channel never orders a read the rewrite does
    /// not make (the rewrite demands what this channel leaves unordered).
    /// </summary>
    private static LiftingCallee SiblingWalkCalleeKind(Expr callee, SiblingWalkContext context, ShadowScope shadow)
    {
        switch (callee.UnwrapGraceOperand())
        {
            case Expr.Resolve { ElaboratedMathMember: not null } opened when !shadow.Shadows(opened.Name):
                return LiftingCallee.StrictValue;

            case Expr.Resolve resolve:
                return shadow.Shadows(resolve.Name)
                    ? LiftingCallee.Dynamic
                    : context.Lookup?.CalleeKindOf(resolve.Name) ?? SiblingWalkPreludeCalleeKind(resolve, shadow);

            case Expr.DotCall { Args: null } edge when edge.TryGetRegistryProvenCanonicalMathFacts(shadow.PreludeNameShadowed, out _):
                return LiftingCallee.StrictValue;

            case Expr.AlgorithmExpr:
                return LiftingCallee.User;

            default:
                return LiftingCallee.Dynamic;
        }
    }

    /// <summary>
    /// Without the resolver's lookup (a standalone build): the prelude by the registry — an
    /// unshadowed Math alias is a strict-value callee, an unshadowed builtin name the builtin.
    /// </summary>
    private static LiftingCallee SiblingWalkPreludeCalleeKind(Expr.Resolve callee, ShadowScope shadow)
    {
        if (shadow.PreludeNameShadowed(callee.Name))
            return LiftingCallee.Dynamic;
        if (callee.TryGetRegistryProvenMathAliasFacts(shadow.PreludeNameShadowed, out _))
            return LiftingCallee.StrictValue;
        foreach (var descriptor in BuiltinRegistry.AllBuiltins)
        {
            if (descriptor.Name == callee.Name)
                return LiftingCallee.OfBuiltin(descriptor.Id);
        }

        return LiftingCallee.Dynamic;
    }

    private static HashSet<string> CreateNameSet(IEnumerable<string>? names = null)
        => names is null
            ? new HashSet<string>(StringComparer.Ordinal)
            : new HashSet<string>(names, StringComparer.Ordinal);
}
