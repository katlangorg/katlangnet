using System.Collections.Immutable;

namespace KatLang;

/// <summary>
/// The BOUND OWNERS of an exposure settlement: the algorithms whose own parameters the walk has already
/// supplied, so a requirement one of them owns is not charged outward (<see cref="PendingReference.BoundOwners"/>,
/// accumulated along a settlement by <c>PropertyExposureResolver.PendingResolution</c>). Null stands for no bound
/// owner; a set is never empty.
///
/// <para><see cref="With"/> extends a persistent set, sharing the unaffected nodes. Two sets are equal
/// exactly when they contain the same owners by reference. Equality checks the count and an
/// order-independent fingerprint first, then verifies membership on a fingerprint match.</para>
///
/// <para>Implementation only. Formerly every settlement frame copied its whole set and then sorted and joined
/// every owner id into key text. On a lifted-terminal chain the accumulated sets grow with chain depth.
/// Now only the incoming reference's owners are offered to the set. Distinct sets are retained only by
/// the walks and caches that use them.</para>
/// </summary>
internal sealed class BoundOwnerSet : IEquatable<BoundOwnerSet>
{
    private static readonly ImmutableHashSet<Algorithm> NoOwners =
        ImmutableHashSet.Create<Algorithm>(ReferenceEqualityComparer.Instance);

    private readonly ImmutableHashSet<Algorithm> _owners;
    private readonly ulong _xor;
    private readonly ulong _sum;
    private readonly FrontEndTraversalObservations? _observations;

    private BoundOwnerSet(ImmutableHashSet<Algorithm> owners, ulong xor, ulong sum, long legacyKeyLength,
        FrontEndTraversalObservations? observations)
    {
        _owners = owners;
        _xor = xor;
        _sum = sum;
        LegacyKeyLength = legacyKeyLength;
        _observations = observations;
    }

    public int Count => _owners.Count;

    // The share's admission charge used the decimal ids plus separators. Accumulate the length
    // when an owner is inserted so the same keys fit without forming or walking any key text.
    internal long LegacyKeyLength { get; }

    public bool Contains(Algorithm owner) => _owners.Contains(owner);

    /// <summary>
    /// <paramref name="current"/> (null: none) extended by <paramref name="owners"/>: <paramref name="current"/>
    /// itself when it already holds them all, and null when there is no owner at all.
    /// </summary>
    public static BoundOwnerSet? With(BoundOwnerSet? current, IReadOnlyList<Algorithm> owners, FrontEndTraversalObservations? observations)
    {
        var extended = current?._owners ?? NoOwners;
        var xor = current?._xor ?? 0;
        var sum = current?._sum ?? 0;
        var keyLength = current?.LegacyKeyLength ?? -1; // The first insertion has no separator.
        observations?.RecordSettlementBoundOwnerVisits(owners.Count);
        for (var i = 0; i < owners.Count; i++)
        {
            var next = extended.Add(owners[i]);
            if (ReferenceEquals(next, extended))
                continue;
            extended = next;
            var id = OwnerQualifiedParameter.OwnerKey(owners[i]);
            var mixed = Mix(unchecked((ulong)id));
            xor ^= mixed;
            sum = unchecked(sum + mixed);
            keyLength += DecimalLength(id) + 1;
        }

        if (current is not null && ReferenceEquals(extended, current._owners))
            return current;
        return extended.Count == 0 ? null : new BoundOwnerSet(extended, xor, sum, keyLength, observations);
    }

    public bool Equals(BoundOwnerSet? other)
    {
        if (ReferenceEquals(this, other))
            return true;
        if (other is null || _owners.Count != other._owners.Count || _xor != other._xor || _sum != other._sum)
            return false;
        if (ReferenceEquals(_owners, other._owners))
            return true;

        // Equal counts: the sets are equal exactly when this one holds every owner of the other.
        _observations?.RecordSettlementBoundOwnerVisits(_owners.Count);
        foreach (var owner in other._owners)
        {
            if (!_owners.Contains(owner))
                return false;
        }

        return true;
    }

    public override bool Equals(object? obj) => Equals(obj as BoundOwnerSet);

    public override int GetHashCode() => unchecked((int)(_xor ^ (_xor >> 32)) * 31 + (int)(_sum ^ (_sum >> 32)));

    private static int DecimalLength(long id)
    {
        var length = 1;
        while (id >= 10)
        {
            id /= 10;
            length++;
        }
        return length;
    }

    // SplitMix64's finalizer: owner ids are small consecutive integers, which XOR and addition alone would
    // let cancel between different sets far too easily.
    private static ulong Mix(ulong value)
    {
        unchecked
        {
            value += 0x9E3779B97F4A7C15;
            value = (value ^ (value >> 30)) * 0xBF58476D1CE4E5B9;
            value = (value ^ (value >> 27)) * 0x94D049BB133111EB;
            return value ^ (value >> 31);
        }
    }
}
