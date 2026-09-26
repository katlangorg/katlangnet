using System.Collections.Immutable;
using System.Collections.ObjectModel;
using Requirement = KatLang.PropertyExposureResolver.Requirement;

namespace KatLang;

/// <summary>
/// FE-4a: the exposure resolver's REQUIREMENT SUMMARY of one property — the owner-qualified inputs its
/// value (transitively) requires that only an enclosing owner's call binds — as a CANONICAL IMMUTABLE
/// SET built by a <see cref="RequirementSetInterner"/>. An element is a <see cref="Requirement"/>: the
/// input's name AND the exact owning scope that binds it (by reference), so two same-named parameters
/// of different owners are two elements and never collapse. Within one interner equal content is the
/// SAME node, so K properties whose summaries are equal share one set whatever path derived it, and
/// comparing two summaries is one reference comparison. A set is immutable and references no interner
/// state; <see cref="Origin"/> only names the interner that built it, so a later run reading it (a
/// deferred region's demand-time elaboration reads the eager run's ancestor summaries) re-interns it
/// instead of combining keys from two interners.
/// </summary>
internal readonly struct RequirementSet : IEquatable<RequirementSet>
{
    internal RequirementSet(RequirementSetInterner.Node? root, object origin)
    {
        Root = root;
        Origin = root is null ? null : origin;
    }

    internal RequirementSetInterner.Node? Root { get; }

    /// <summary>The identity token of the interner that built the set (null for the empty set).</summary>
    internal object? Origin { get; }

    public int Count => Root?.Count ?? 0;

    public bool IsEmpty => Root is null;

    /// <summary>The set's elements in the interner's key order (callers must not depend on it).</summary>
    public IEnumerable<Requirement> Elements => RequirementSetInterner.EnumerateElements(Root);

    /// <summary>Exact content identity within one interner.</summary>
    public bool Equals(RequirementSet other) => ReferenceEquals(Root, other.Root);

    public override bool Equals(object? obj) => obj is RequirementSet other && Equals(other);

    public override int GetHashCode() => Root?.Id ?? 0;
}

/// <summary>
/// FE-4a: the run-local interner of <see cref="RequirementSet"/>s — the owner-qualified instance of
/// the one canonical-set engine (<see cref="CanonicalSetInterner{TElement}"/>). Element identity is
/// <see cref="Requirement"/>'s exact equality: ordinal name AND owning scope by reference; spelling
/// alone never identifies a required ancestor. One interner serves one exposure resolution (never
/// static); it is garbage afterwards except for the immutable sets the run leaves in retained summary
/// scopes. Every combination ADOPTS its operands first, so a set another run built is re-interned by
/// its elements (once per foreign set per run) and interner keys are never mixed.
/// </summary>
internal sealed class RequirementSetInterner(FrontEndTraversalObservations? observations)
    : CanonicalSetInterner<Requirement>(EqualityComparer<Requirement>.Default)
{
    private readonly object _origin = new();
    private Dictionary<Node, RequirementSet>? _adopted;
    private Dictionary<Node, Node>? _derivationBases;
    private Dictionary<Node, Node>? _sharingCores;

    /// <summary>The canonical set of <paramref name="requirements"/>.</summary>
    public RequirementSet From(IEnumerable<Requirement> requirements) => Wrap(WithElements(null, requirements));

    /// <summary>
    /// The canonical union; the larger side is SHARED, and equal operands return themselves. A result
    /// that is neither operand records its larger operand as its DERIVATION BASE (the first union to
    /// produce the set decides): a subset it was built from, which the output projection may extend by
    /// the difference instead of copying the base (<see cref="RequiredAncestorOutputs"/>).
    /// </summary>
    public RequirementSet Union(RequirementSet first, RequirementSet second)
    {
        var left = Adopt(first).Root;
        var right = Adopt(second).Root;
        var union = UnionRoots(left, right);
        if (left is not null && right is not null && !ReferenceEquals(union, left) && !ReferenceEquals(union, right))
        {
            _derivationBases ??= new(ReferenceEqualityComparer.Instance);
            if (!_derivationBases.ContainsKey(union!))
            {
                var basis = left.Count >= right.Count ? left : right;
                // (A + small delta) union B must extend the shared A union B, rather than
                // materializing the two large halves again for every delta. Core lookup is
                // constant-time; no recursive walk of a long derivation chain is needed.
                var leftCore = SharingCore(left);
                var rightCore = SharingCore(right);
                if (!ReferenceEquals(leftCore, left) || !ReferenceEquals(rightCore, right))
                {
                    var common = UnionRoots(leftCore, rightCore)!;
                    if (common.Count > basis.Count && common.Count < union!.Count)
                        basis = common;
                }
                _derivationBases.Add(union!, basis);
                var core = SharingCore(basis);
                if (core.Count >= RequiredAncestorOutputs.MinimumDerivationBase
                    && (long)(union!.Count - core.Count) * 4 <= core.Count)
                    (_sharingCores ??= new(ReferenceEqualityComparer.Instance)).Add(union, core);
            }
        }
        return Wrap(union);
    }

    private Node SharingCore(Node node)
        => _sharingCores is not null && _sharingCores.TryGetValue(node, out var core) ? core : node;

    /// <summary>The elements of <paramref name="set"/> that are not in <paramref name="subtrahend"/>.</summary>
    public RequirementSet Except(RequirementSet set, RequirementSet subtrahend)
        => Wrap(ExceptRoots(Adopt(set).Root, Adopt(subtrahend).Root));

    /// <summary>The derivation base recorded for <paramref name="set"/> (see <see cref="Union"/>), if any.</summary>
    public bool TryGetDerivationBase(RequirementSet set, out RequirementSet derivationBase)
    {
        if (set.Root is { } root && ReferenceEquals(set.Origin, _origin)
            && _derivationBases is not null && _derivationBases.TryGetValue(root, out var baseRoot))
        {
            derivationBase = Wrap(baseRoot);
            return true;
        }

        derivationBase = default;
        return false;
    }

    /// <summary>
    /// <paramref name="set"/> as a set of THIS interner: itself when this interner built it, otherwise
    /// the canonical set of its elements (the elements, owner scopes included, are unchanged).
    /// </summary>
    public RequirementSet Adopt(RequirementSet set)
    {
        if (set.Root is not { } root || ReferenceEquals(set.Origin, _origin))
            return set;

        _adopted ??= new(ReferenceEqualityComparer.Instance);
        if (!_adopted.TryGetValue(root, out var adopted))
        {
            adopted = From(set.Elements);
            _adopted.Add(root, adopted);
        }

        return adopted;
    }

    private RequirementSet Wrap(Node? root) => new(root, _origin);

    protected override void RecordElementCanonicalized() => observations?.RecordRequiredAncestorElementCanonicalized();

    protected override void RecordOperationStep() => observations?.RecordRequiredAncestorSetOperationStep();
}

/// <summary>
/// FE-4a: the run-scoped projection of final requirement sets into the two per-property output lists —
/// the public <see cref="Property.RequiredAncestorParameters"/> (the distinct required NAMES, sorted
/// ordinally) and the internal <see cref="Property.CaptureRequirements"/> (every requirement as its name
/// and owner depth relative to the property's declaring scope, sorted by name then depth). Each list is
/// materialized ONCE per distinct set. Each property's distinct <see cref="RequiredAncestorList{T}"/>
/// wrapper references that backing, so K properties requiring the same W inputs retain W entries
/// plus K wrappers, preserving record equality instead of canonicalizing the property list identity.
///
/// <para><b>Exact content.</b> A list's content is its whole meaning — names for the public list,
/// owner-RELATIVE (name, depth) pairs for the internal one, which the evaluator resolves from each
/// property's own declaring scope — so equal content is equal meaning, and sharing a list never merges
/// properties, declarations, or owner activations. Flat lists are additionally shared across sets by
/// exact content (equality is element-by-element; the hash only selects a bucket), so two owners whose
/// requirements have the same relative shape share one list too.</para>
///
/// <para><b>Structural sharing for overlapping sets.</b> A set the interner derived from a much larger
/// subset (<see cref="RequirementSetInterner.TryGetDerivationBase"/>: at least
/// <see cref="MinimumDerivationBase"/> elements, extended by at most a quarter of them) is projected
/// into a PERSISTENT list that extends the base's persistent list by the difference: an immutable
/// sorted set of names, an immutable sorted list of captures. Such a list shares every untouched node
/// with its base, so K properties that each add a few inputs to one W-wide requirement set cost
/// O(W + K × delta × log W) instead of K × W. Derivation chains are walked iteratively.</para>
///
/// <para><b>Immutable.</b> Every list is immutable — a <see cref="ReadOnlyCollection{T}"/> over a private
/// array, an <see cref="ImmutableSortedSet{T}"/>, or an <see cref="ImmutableList{T}"/> — so no holder can
/// change another holder's list, and no list references anything but its elements. The memo tables are
/// garbage after the run.</para>
/// </summary>
internal sealed class RequiredAncestorOutputs(RequirementSetInterner sets, FrontEndTraversalObservations? observations)
{
    /// <summary>The smallest base a set is derived from rather than materialized flat.</summary>
    internal const int MinimumDerivationBase = 16;

    private static readonly Comparison<CapturedParameterRequirement> CaptureOrder = static (left, right) =>
    {
        var byName = StringComparer.Ordinal.Compare(left.Name, right.Name);
        return byName != 0 ? byName : left.OwnerDepth.CompareTo(right.OwnerDepth);
    };

    private static readonly IComparer<CapturedParameterRequirement> CaptureComparer = Comparer<CapturedParameterRequirement>.Create(CaptureOrder);

    private Dictionary<RequirementSetInterner.Node, IReadOnlyList<string>>? _namesBySet;
    private Dictionary<string[], ReadOnlyCollection<string>>? _namesByContent;
    private Dictionary<RequirementSetInterner.Node, ImmutableSortedSet<string>>? _nameTrees;
    private Dictionary<RequirementSetInterner.Node, ElaboratedPropertyScope?[]>? _ownersBySet;
    private Dictionary<(RequirementSetInterner.Node Set, int[] Depths), IReadOnlyList<CapturedParameterRequirement>>? _capturesBySetAndDepths;
    private Dictionary<CapturedParameterRequirement[], ReadOnlyCollection<CapturedParameterRequirement>>? _capturesByContent;
    private Dictionary<(RequirementSetInterner.Node Set, int[] Depths), ImmutableList<CapturedParameterRequirement>>? _captureTrees;

    /// <summary>The distinct required names of <paramref name="set"/>, sorted ordinally.</summary>
    public IReadOnlyList<string> Names(RequirementSet set)
    {
        if (set.Root is not { } root)
            return [];

        _namesBySet ??= new(ReferenceEqualityComparer.Instance);
        if (_namesBySet.TryGetValue(root, out var shared))
            return shared;

        var chain = DerivationChain(set, node => _nameTrees?.ContainsKey(node) == true);
        shared = chain.Count > 1 ? DeriveNames(chain) : FlatNames(set);
        _namesBySet.Add(root, shared);
        return shared;
    }

    /// <summary>
    /// Every requirement of <paramref name="set"/> as (name, owner depth), sorted by name then depth;
    /// <paramref name="ownerDepth"/> is the declaring level's depth of an owning scope (-1 when the
    /// owner is not on its chain). A list is keyed by the set and the depths of its DISTINCT owners (a
    /// handful — owners are levels of one lexical chain), so K properties of one level, or of K sibling
    /// levels at the same distance from the owners, share one list without re-deriving it.
    /// </summary>
    public IReadOnlyList<CapturedParameterRequirement> Captures(
        RequirementSet set,
        Func<ElaboratedPropertyScope?, int> ownerDepth)
    {
        if (set.Root is not { } root)
            return Array.Empty<CapturedParameterRequirement>();

        var depths = DepthsOf(set, ownerDepth);
        _capturesBySetAndDepths ??= new(CaptureKeyComparer.Instance);
        if (_capturesBySetAndDepths.TryGetValue((root, depths), out var shared))
            return shared;

        var chain = DerivationChain(set, node => _captureTrees?.ContainsKey((node, DepthsOf(new RequirementSet(node, set.Origin!), ownerDepth))) == true);
        shared = chain.Count > 1 ? DeriveCaptures(chain, ownerDepth) : FlatCaptures(set, depths);
        _capturesBySetAndDepths.Add((root, depths), shared);
        return shared;
    }

    // [S, B1, ..., Bm]: each element the eligible derivation base of the previous one, stopping at a set
    // with no eligible base or with a persistent list already built.
    private List<RequirementSet> DerivationChain(RequirementSet set, Func<RequirementSetInterner.Node, bool> hasPersistentList)
    {
        var chain = new List<RequirementSet> { set };
        var current = set;
        while (sets.TryGetDerivationBase(current, out var derivationBase)
            && derivationBase.Count >= MinimumDerivationBase
            && (long)(current.Count - derivationBase.Count) * 4 <= derivationBase.Count)
        {
            chain.Add(derivationBase);
            if (hasPersistentList(derivationBase.Root!))
                break;
            current = derivationBase;
        }

        return chain;
    }

    private ReadOnlyCollection<string> FlatNames(RequirementSet set)
    {
        var names = new HashSet<string>(StringComparer.Ordinal);
        foreach (var requirement in set.Elements)
            names.Add(requirement.Name);
        var sorted = names.ToArray();
        Array.Sort(sorted, StringComparer.Ordinal);

        _namesByContent ??= new(new ExactSequenceComparer<string>(StringComparer.Ordinal));
        if (!_namesByContent.TryGetValue(sorted, out var shared))
        {
            shared = new ReadOnlyCollection<string>(sorted);
            _namesByContent.Add(sorted, shared);
            observations?.RecordRequiredAncestorListMaterialized(sorted.Length);
        }

        return shared;
    }

    private ImmutableSortedSet<string> DeriveNames(List<RequirementSet> chain)
    {
        _nameTrees ??= new(ReferenceEqualityComparer.Instance);
        var last = chain[^1];
        if (!_nameTrees.TryGetValue(last.Root!, out var tree))
        {
            var flat = Names(last);
            tree = ImmutableSortedSet.CreateRange(StringComparer.Ordinal, flat);
            _nameTrees.Add(last.Root!, tree);
            observations?.RecordRequiredAncestorPersistentBase(flat.Count);
        }

        for (var k = chain.Count - 2; k >= 0; k--)
        {
            var delta = sets.Except(chain[k], chain[k + 1]);
            foreach (var requirement in delta.Elements)
                tree = tree.Add(requirement.Name);
            _nameTrees.TryAdd(chain[k].Root!, tree);
            observations?.RecordRequiredAncestorListDerived(delta.Count);
        }

        return tree;
    }

    private ReadOnlyCollection<CapturedParameterRequirement> FlatCaptures(RequirementSet set, int[] depths)
    {
        var owners = OwnersOf(set);
        var captures = new CapturedParameterRequirement[set.Count];
        var index = 0;
        foreach (var requirement in set.Elements)
            captures[index++] = new CapturedParameterRequirement(requirement.Name, depths[Array.IndexOf(owners, requirement.Owner)]);
        Array.Sort(captures, CaptureOrder);

        _capturesByContent ??= new(new ExactSequenceComparer<CapturedParameterRequirement>(EqualityComparer<CapturedParameterRequirement>.Default));
        if (!_capturesByContent.TryGetValue(captures, out var shared))
        {
            shared = new ReadOnlyCollection<CapturedParameterRequirement>(captures);
            _capturesByContent.Add(captures, shared);
            observations?.RecordRequiredAncestorListMaterialized(captures.Length);
        }

        return shared;
    }

    private ImmutableList<CapturedParameterRequirement> DeriveCaptures(List<RequirementSet> chain, Func<ElaboratedPropertyScope?, int> ownerDepth)
    {
        _captureTrees ??= new(CaptureKeyComparer.Instance);
        var last = chain[^1];
        var lastKey = (last.Root!, DepthsOf(last, ownerDepth));
        if (!_captureTrees.TryGetValue(lastKey, out var tree))
        {
            var flat = Captures(last, ownerDepth);
            tree = ImmutableList.CreateRange(flat);
            _captureTrees.Add(lastKey, tree);
            observations?.RecordRequiredAncestorPersistentBase(flat.Count);
        }

        for (var k = chain.Count - 2; k >= 0; k--)
        {
            var delta = sets.Except(chain[k], chain[k + 1]);
            foreach (var requirement in delta.Elements)
            {
                var capture = new CapturedParameterRequirement(requirement.Name, ownerDepth(requirement.Owner));
                var position = tree.BinarySearch(capture, CaptureComparer);
                tree = tree.Insert(position < 0 ? ~position : position, capture);
            }

            _captureTrees.TryAdd((chain[k].Root!, DepthsOf(chain[k], ownerDepth)), tree);
            observations?.RecordRequiredAncestorListDerived(delta.Count);
        }

        return tree;
    }

    private int[] DepthsOf(RequirementSet set, Func<ElaboratedPropertyScope?, int> ownerDepth)
    {
        var owners = OwnersOf(set);
        var depths = new int[owners.Length];
        for (var i = 0; i < owners.Length; i++)
            depths[i] = ownerDepth(owners[i]);
        return depths;
    }

    // The distinct owning scopes of a set's requirements — once per set. A set with a derivation base
    // extends its base's owners by those of the elements the base lacks, so a derived set never
    // re-enumerates the base it shares (the chain is walked iteratively to a set with known owners).
    private ElaboratedPropertyScope?[] OwnersOf(RequirementSet set)
    {
        _ownersBySet ??= new(ReferenceEqualityComparer.Instance);
        if (_ownersBySet.TryGetValue(set.Root!, out var owners))
            return owners;

        var chain = new List<RequirementSet> { set };
        var current = set;
        while (owners is null && sets.TryGetDerivationBase(current, out var derivationBase))
        {
            chain.Add(derivationBase);
            _ownersBySet.TryGetValue(derivationBase.Root!, out owners);
            current = derivationBase;
        }

        if (owners is null)
        {
            owners = Extend([], chain[^1]);
            _ownersBySet.Add(chain[^1].Root!, owners);
        }

        for (var k = chain.Count - 2; k >= 0; k--)
        {
            owners = Extend(owners, sets.Except(chain[k], chain[k + 1]));
            _ownersBySet.TryAdd(chain[k].Root!, owners);
        }

        return owners;

        static ElaboratedPropertyScope?[] Extend(ElaboratedPropertyScope?[] known, RequirementSet elements)
        {
            List<ElaboratedPropertyScope?>? extended = null;
            foreach (var requirement in elements.Elements)
            {
                if (Array.IndexOf(known, requirement.Owner) < 0
                    && (extended is null || !extended.Contains(requirement.Owner, ReferenceEqualityComparer.Instance)))
                    (extended ??= []).Add(requirement.Owner);
            }

            return extended is null ? known : [.. known, .. extended];
        }
    }

    private sealed class CaptureKeyComparer : IEqualityComparer<(RequirementSetInterner.Node Set, int[] Depths)>
    {
        public static readonly CaptureKeyComparer Instance = new();

        public bool Equals((RequirementSetInterner.Node Set, int[] Depths) x, (RequirementSetInterner.Node Set, int[] Depths) y)
            => ReferenceEquals(x.Set, y.Set) && x.Depths.AsSpan().SequenceEqual(y.Depths);

        public int GetHashCode((RequirementSetInterner.Node Set, int[] Depths) key)
        {
            var hash = new HashCode();
            hash.Add(key.Set.Id);
            foreach (var depth in key.Depths)
                hash.Add(depth);
            return hash.ToHashCode();
        }
    }

    /// <summary>
    /// Exact element-by-element list equality — the one proof two lists may share. The hash only
    /// selects a bucket: two different contents whose hashes collide are still different lists.
    /// </summary>
    internal sealed class ExactSequenceComparer<T>(IEqualityComparer<T> elements) : IEqualityComparer<T[]>
    {
        public bool Equals(T[]? x, T[]? y)
        {
            if (ReferenceEquals(x, y))
                return true;
            if (x is null || y is null || x.Length != y.Length)
                return false;
            for (var i = 0; i < x.Length; i++)
            {
                if (!elements.Equals(x[i], y[i]))
                    return false;
            }

            return true;
        }

        public int GetHashCode(T[] items)
        {
            var hash = new HashCode();
            hash.Add(items.Length);
            foreach (var item in items)
                hash.Add(item is null ? 0 : elements.GetHashCode(item));
            return hash.ToHashCode();
        }
    }
}

/// <summary>
/// One property's collection identity over immutable, shared backing. Generated Property equality
/// has always compared list references: canonicalizing storage must not canonicalize that identity.
/// Copies of the property retain the wrapper; distinct elaborated properties get distinct wrappers.
/// The historical array label keeps Property's generated debug text independent of backing choice.
/// No analysis state or mutable builder is retained.
/// </summary>
internal sealed class RequiredAncestorList<T>(IReadOnlyList<T> backing) : IReadOnlyList<T>
{
    internal IReadOnlyList<T> Backing { get; } = backing;
    public int Count => Backing.Count;
    public T this[int index] => Backing[index];
    public IEnumerator<T> GetEnumerator() => Backing.GetEnumerator();
    System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();
    public override string ToString() => typeof(T[]).ToString();

    internal static IReadOnlyList<T> ForProperty(IReadOnlyList<T> backing)
        => backing.Count == 0 ? backing : new RequiredAncestorList<T>(backing);
}
