using System.Buffers;
using System.Collections.ObjectModel;
using System.Runtime.CompilerServices;

namespace KatLang;

/// <summary>
/// The ONE read-only view KatLang publishes over storage it owns or shares: a
/// <see cref="ReadOnlyCollection{T}"/> whose non-generic <see cref="System.Collections.ICollection.SyncRoot"/>
/// is the view itself.
///
/// <para><b>Why.</b> <see cref="ReadOnlyCollection{T}"/> answers <c>SyncRoot</c> with the wrapped
/// collection's own <c>SyncRoot</c>; an array's is the array and a <see cref="List{T}"/>'s is the
/// list. So <c>Array.AsReadOnly(array)</c> and <c>list.AsReadOnly()</c> hand their writable storage to
/// any caller with one cast and no reflection
/// (<c>(Result[])((System.Collections.ICollection)value.Items).SyncRoot</c>), and a write through it
/// changes a value, a catalog, or an interned list that the engine treats as immutable.</para>
///
/// <para><b>What changes.</b> Only <c>SyncRoot</c>. Re-listing <see cref="System.Collections.ICollection"/>
/// re-implements that one member; every other member of the interface — and every other interface
/// the base implements — still maps onto the base class, so counts, indexing, copying, enumeration,
/// and the rejection of every mutation member are the BCL's. The view adds no field, so it costs
/// the same one object as the plain collection, and <c>is ReadOnlyCollection&lt;T&gt;</c> stays true.
/// <see cref="ToString"/> keeps the plain collection's text, so the debug text of a record holding a
/// view is unchanged.</para>
///
/// <para><b>Use.</b> Build one with <see cref="SafeReadOnlyCollection.Over{T}(T[])"/> or
/// <see cref="SafeReadOnlyCollection.OverList{T}(IList{T})"/>. <c>Array.AsReadOnly</c>,
/// <c>List&lt;T&gt;.AsReadOnly()</c>, <c>new ReadOnlyCollection&lt;T&gt;(…)</c> and a class deriving from
/// <see cref="ReadOnlyCollection{T}"/> directly are refused in this assembly by
/// <c>ReadOnlyViewSourcePolicyTests</c>.</para>
///
/// <para><b>Boundary.</b> The guarantee is about safe managed code using public API, casts and
/// interface members. Reflection, <c>unsafe</c> code and the marshalling helpers
/// (<c>MemoryMarshal</c>, <c>CollectionsMarshal</c>, <c>ImmutableCollectionsMarshal</c>,
/// <c>Unsafe</c>) are outside it, and so is storage a host supplied and still owns. See
/// <c>docs/design/language-rules/evaluator-and-hosting.md</c>, Read-only views never hand out
/// their storage.</para>
/// </summary>
internal class SafeReadOnlyCollection<T>(IList<T> items) : ReadOnlyCollection<T>(items), System.Collections.ICollection
{
    /// <summary>
    /// The shared view of no items, as <see cref="ReadOnlyCollection{T}.Empty"/> is for the plain
    /// collection: immutable and stateless, so every empty value shares it and allocates no view.
    /// </summary>
    internal static new readonly SafeReadOnlyCollection<T> Empty = new(Array.Empty<T>());

    /// <summary>The view itself, on every read and through every interface: never the wrapped storage.</summary>
    object System.Collections.ICollection.SyncRoot => this;

    /// <summary>The plain collection's text: a view is an implementation detail of the record that holds it.</summary>
    public override string ToString()
        => GetType() == typeof(SafeReadOnlyCollection<T>) ? typeof(ReadOnlyCollection<T>).ToString() : base.ToString()!;
}

/// <summary>The constructors of <see cref="SafeReadOnlyCollection{T}"/>.</summary>
internal static class SafeReadOnlyCollection
{
    /// <summary>A read-only view of a private snapshot of caller-supplied items.</summary>
    internal static ReadOnlyCollection<T> Snapshot<T>(IEnumerable<T> source) => Over(CopyHostInput(source));

    /// <summary>
    /// Snapshots caller-owned membership without passing the destination array to caller code.
    /// LINQ's bulk copy can invoke the source's <c>ICollection&lt;T&gt;.CopyTo</c>, including through
    /// a composed query. Only bulk-copy sources whose implementation and backing we own or know.
    ///
    /// <para>Every other source is ENUMERATED, exactly once, and supplies its elements through that
    /// enumeration alone: a caller-defined list is never read through <c>Count</c> and its indexer
    /// instead, even when it implements <see cref="IReadOnlyList{T}"/>. A host sees the one
    /// <c>GetEnumerator</c> call it always saw, the snapshot holds what that enumeration produced, in
    /// its order, and an exception the enumeration throws escapes to the caller
    /// (<see cref="RunOptions.AllowedHosts"/> documents both).</para>
    /// </summary>
    internal static T[] CopyHostInput<T>(IEnumerable<T> source)
    {
        if (source is T[] or SafeReadOnlyCollection<T> || source.GetType() == typeof(List<T>))
            return source.ToArray();

        return CopyEnumerable(source);
    }

    // A one-pass source may have no count. Keep small inputs inline and rent temporary space for
    // longer streams. Only the exact final array escapes. This needs no per-snapshot adapter object.
    // A count the source reports without being enumerated only SIZES the private copy; it never
    // decides the content, so a source whose count disagrees with its enumeration is still copied
    // exactly as enumerated.
    [InlineArray(8)]
    private struct FirstItems<T>
    {
        private T _first;
    }

    private static T[] CopyEnumerable<T>(IEnumerable<T> source)
    {
        FirstItems<T> first = default;
        Span<T> buffer = first;
        var exact = source.TryGetNonEnumeratedCount(out var count) && count > 0 ? new T[count] : null;
        if (exact is not null)
            buffer = exact;
        T[]? rented = null;
        int used = 0;
        try
        {
            foreach (var item in source)
            {
                if (used == buffer.Length)
                {
                    if (used == Array.MaxLength)
                        throw new OutOfMemoryException();
                    var capacity = (int)Math.Min(Array.MaxLength, 2L * used);
                    var next = ArrayPool<T>.Shared.Rent(capacity);
                    buffer.CopyTo(next);
                    if (rented is not null)
                        ArrayPool<T>.Shared.Return(rented, RuntimeHelpers.IsReferenceOrContainsReferences<T>());
                    buffer = rented = next;
                }
                buffer[used++] = item;
            }
            return rented is null && exact is not null && exact.Length == used ? exact : buffer[..used].ToArray();
        }
        finally
        {
            if (rented is not null)
                ArrayPool<T>.Shared.Return(rented, RuntimeHelpers.IsReferenceOrContainsReferences<T>());
        }
    }

    /// <summary>
    /// A read-only view over <paramref name="exclusivelyOwned"/>, WITHOUT copying it: the array
    /// belongs to the view from here on, and the caller must not write to it, reuse it, or expose
    /// it. An empty array yields the shared empty view, exactly as <c>Array.AsReadOnly</c> yields
    /// <see cref="ReadOnlyCollection{T}.Empty"/>.
    /// </summary>
    internal static ReadOnlyCollection<T> Over<T>(T[] exclusivelyOwned)
    {
        ArgumentNullException.ThrowIfNull(exclusivelyOwned);
        return exclusivelyOwned.Length == 0
            ? SafeReadOnlyCollection<T>.Empty
            : new SafeReadOnlyCollection<T>(exclusivelyOwned);
    }

    /// <summary>
    /// A distinct read-only view over <paramref name="source"/>, which it reads in place: a
    /// <see cref="List{T}"/> still being filled (the view sees later additions), another
    /// read-only list whose identity the wrapper must not share, or a name list one diagnostic
    /// record owns (a record compares its list by reference, so each failure needs its own).
    /// Never the shared empty view, even while the source is empty.
    /// </summary>
    internal static ReadOnlyCollection<T> OverList<T>(IList<T> source)
        => new SafeReadOnlyCollection<T>(source);
}
