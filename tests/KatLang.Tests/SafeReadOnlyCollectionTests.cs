using System.Collections;
using System.Collections.ObjectModel;
using System.Reflection;
using KatLang.Semantics;

namespace KatLang.Tests;

/// <summary>
/// <see cref="SafeReadOnlyCollection{T}"/> (November 2026): the read-only view KatLang publishes,
/// a <see cref="ReadOnlyCollection{T}"/> whose non-generic <see cref="ICollection.SyncRoot"/> is
/// the view itself instead of the wrapped array or list. It re-lists <see cref="ICollection"/> and
/// re-implements that ONE member; these tests confirm, in this repository's build, that every other
/// member still maps onto the base class — so the view inherits the BCL's behavior — and that the
/// helper costs no field. The attack this closes is pinned through the public API alone by
/// <c>ReadOnlyViewStorageContractTests</c> and <c>PublicCollectionStorageSweepTests</c>.
/// </summary>
public class SafeReadOnlyCollectionTests
{
    private static readonly Result[] Atoms = [new Result.Atom(1), new Result.Atom(2), new Result.Atom(3)];

    private static Result[] FreshAtoms() => [.. Atoms];

    /// <summary>
    /// The canary: the plain BCL views still hand out their storage. When a runtime changes this,
    /// the helper can be retired; until then nothing in <c>src/KatLang</c> may publish one.
    /// </summary>
    [Fact]
    public void ThePlainCollection_StillHandsOutItsStorage()
    {
        var array = FreshAtoms();
        Assert.Same(array, ((ICollection)Array.AsReadOnly(array)).SyncRoot);
        var list = new List<Result>(Atoms);
        Assert.Same(list, ((ICollection)list.AsReadOnly()).SyncRoot);
        Assert.Same(array, ((ICollection)new ReadOnlyCollection<Result>(array)).SyncRoot);
    }

    [Fact]
    public void SyncRoot_IsTheViewItself_ThroughEveryStaticType()
    {
        foreach (var view in new[] { SafeReadOnlyCollection.Over(FreshAtoms()), SafeReadOnlyCollection.OverList(new List<Result>(Atoms)) })
        {
            var derived = Assert.IsAssignableFrom<SafeReadOnlyCollection<Result>>(view);
            ReadOnlyCollection<Result> plain = view;
            IList nonGenericList = view;
            ICollection nonGeneric = view;
            IList<Result> genericList = view;
            IReadOnlyList<Result> readOnly = view;

            Assert.Same(view, ((ICollection)derived).SyncRoot);
            Assert.Same(view, ((ICollection)plain).SyncRoot);
            Assert.Same(view, nonGenericList.SyncRoot);
            Assert.Same(view, nonGeneric.SyncRoot);
            Assert.Same(view, ((ICollection)genericList).SyncRoot);
            Assert.Same(view, ((ICollection)readOnly).SyncRoot);
            Assert.Same(nonGeneric.SyncRoot, nonGeneric.SyncRoot);
            Assert.IsNotType<Result[]>(nonGeneric.SyncRoot);
            Assert.IsNotType<List<Result>>(nonGeneric.SyncRoot);
        }
    }

    /// <summary>The members of the re-listed interface that the helper does NOT declare still reach the base class.</summary>
    [Fact]
    public void TheOtherCollectionMembers_StillReachTheBaseClass()
    {
        var plain = Array.AsReadOnly(FreshAtoms());
        var view = SafeReadOnlyCollection.Over(FreshAtoms());
        ICollection nonGeneric = view;

        Assert.Equal(3, nonGeneric.Count);
        Assert.False(nonGeneric.IsSynchronized);

        var copied = new object[4];
        nonGeneric.CopyTo(copied, 1);
        Assert.Null(copied[0]);
        Assert.Equal(Atoms, copied.Skip(1));

        // Refusals are the plain collection's: the same exception type for every bad destination.
        Array[] destinations = [new string[3], new object[2], new object[3, 3], new int[3]];
        foreach (var destination in destinations)
        {
            var expected = Record.Exception(() => ((ICollection)plain).CopyTo(destination, 0));
            var actual = Record.Exception(() => nonGeneric.CopyTo(destination, 0));
            Assert.NotNull(expected);
            Assert.IsType(expected.GetType(), actual);
        }

        Assert.Equal(
            Record.Exception(() => ((ICollection)plain).CopyTo(new object[3], 1))?.GetType(),
            Record.Exception(() => nonGeneric.CopyTo(new object[3], 1))?.GetType());
        Assert.IsType<ArgumentNullException>(Record.Exception(() => nonGeneric.CopyTo(null!, 0)));
    }

    /// <summary>The generic copy still fills a covariant destination, exactly as the plain view does.</summary>
    [Fact]
    public void GenericCopyTo_FillsACovariantAtomArray()
    {
        ICollection<Result> view = SafeReadOnlyCollection.Over(FreshAtoms());
        Result[] destination = new Result.Atom[3];
        view.CopyTo(destination, 0);
        Assert.Equal(Atoms, destination);

        // A destination the items do not fit is refused with the plain view's exception.
        Result[] strings = new Result.Str[3];
        var expected = Record.Exception(() => ((ICollection<Result>)Array.AsReadOnly(FreshAtoms())).CopyTo(strings, 0));
        Assert.NotNull(expected);
        Assert.IsType(expected.GetType(), Record.Exception(() => view.CopyTo(strings, 0)));
    }

    [Fact]
    public void EveryMutationMember_Throws_ThroughBothInterfaceFamilies()
    {
        foreach (var view in new[] { SafeReadOnlyCollection.Over(FreshAtoms()), SafeReadOnlyCollection.OverList(new List<Result>(Atoms)) })
        {
            IList<Result> generic = view;
            Assert.True(generic.IsReadOnly);
            Assert.Throws<NotSupportedException>(() => generic[0] = Atoms[1]);
            Assert.Throws<NotSupportedException>(() => generic.Add(Atoms[0]));
            Assert.Throws<NotSupportedException>(() => generic.Insert(0, Atoms[0]));
            Assert.Throws<NotSupportedException>(() => generic.Remove(Atoms[0]));
            Assert.Throws<NotSupportedException>(() => generic.RemoveAt(0));
            Assert.Throws<NotSupportedException>(generic.Clear);

            IList nonGeneric = view;
            Assert.True(nonGeneric.IsReadOnly);
            Assert.True(nonGeneric.IsFixedSize);
            Assert.Throws<NotSupportedException>(() => nonGeneric[0] = Atoms[1]);
            Assert.Throws<NotSupportedException>(() => nonGeneric.Add(Atoms[0]));
            Assert.Throws<NotSupportedException>(() => nonGeneric.Insert(0, Atoms[0]));
            Assert.Throws<NotSupportedException>(() => nonGeneric.Remove(Atoms[0]));
            Assert.Throws<NotSupportedException>(() => nonGeneric.RemoveAt(0));
            Assert.Throws<NotSupportedException>(nonGeneric.Clear);

            Assert.Equal(Atoms, view);
        }
    }

    /// <summary>Reads through the non-generic list are the plain view's, a foreign argument included.</summary>
    [Fact]
    public void NonGenericReads_AnswerLikeThePlainCollection()
    {
        IList plain = Array.AsReadOnly(FreshAtoms());
        IList view = SafeReadOnlyCollection.Over(FreshAtoms());
        foreach (var probe in new object?[] { Atoms[1], new Result.Atom(2), "text", 7, null })
        {
            Assert.Equal(plain.Contains(probe), view.Contains(probe));
            Assert.Equal(plain.IndexOf(probe), view.IndexOf(probe));
        }

        Assert.Equal(plain[2], view[2]);
        Assert.IsType(
            Record.Exception(() => plain[3])!.GetType(),
            Record.Exception(() => view[3]));
    }

    [Fact]
    public void TheNonGenericEnumerator_IsStillCloneable()
    {
        var plain = ((IEnumerable)Array.AsReadOnly(FreshAtoms())).GetEnumerator();
        var enumerator = ((IEnumerable)SafeReadOnlyCollection.Over(FreshAtoms())).GetEnumerator();
        Assert.IsType(plain.GetType(), enumerator);

        var cloneable = Assert.IsAssignableFrom<ICloneable>(enumerator);
        Assert.True(enumerator.MoveNext());
        var clone = (IEnumerator)cloneable.Clone();
        Assert.Same(Atoms[0], clone.Current);
        Assert.True(clone.MoveNext());
        Assert.Same(Atoms[1], clone.Current);
        Assert.Same(Atoms[0], enumerator.Current);

        enumerator.Reset();
        var seen = new List<object?>();
        while (enumerator.MoveNext())
            seen.Add(enumerator.Current);
        Assert.Equal(Atoms, seen);
    }

    /// <summary>A view over a live list reads it in place, and still never reaches it.</summary>
    [Fact]
    public void AListBackedView_SeesLaterAdditions_AndNeverReachesTheList()
    {
        var source = new List<Result> { Atoms[0] };
        var view = SafeReadOnlyCollection.OverList(source);
        Assert.Single(view);

        source.Add(Atoms[1]);
        source.Add(Atoms[2]);
        Assert.Equal(Atoms, view);
        Assert.Equal(3, view.Count);
        Assert.Same(view, ((ICollection)view).SyncRoot);
        Assert.NotSame(source, ((ICollection)view).SyncRoot);

        // Never the shared empty view: an empty source may be filled later, and wrappers stay distinct.
        var empty = new List<Result>();
        var first = SafeReadOnlyCollection.OverList(empty);
        Assert.NotSame(first, SafeReadOnlyCollection.OverList(empty));
        Assert.NotSame(SafeReadOnlyCollection<Result>.Empty, first);
        empty.Add(Atoms[0]);
        Assert.Single(first);
    }

    /// <summary>
    /// <c>Over</c> transfers ownership: no copy, and one shared view for every empty array — as
    /// <c>Array.AsReadOnly</c> shares <see cref="ReadOnlyCollection{T}.Empty"/>.
    /// </summary>
    [Fact]
    public void Over_WrapsWithoutCopying_AndSharesOneEmptyView()
    {
        var array = FreshAtoms();
        var view = SafeReadOnlyCollection.Over(array);
        // Deliberately breaking the ownership rule to SEE the storage: the view reads the given array.
        array[0] = Atoms[2];
        Assert.Same(Atoms[2], view[0]);

        Assert.Same(SafeReadOnlyCollection<Result>.Empty, SafeReadOnlyCollection.Over(Array.Empty<Result>()));
        Assert.Same(SafeReadOnlyCollection<Result>.Empty, SafeReadOnlyCollection.Over(new Result[0]));
        Assert.Empty(SafeReadOnlyCollection<Result>.Empty);
        Assert.Same(SafeReadOnlyCollection<Result>.Empty, ((ICollection)SafeReadOnlyCollection<Result>.Empty).SyncRoot);
        Assert.NotSame(ReadOnlyCollection<Result>.Empty, SafeReadOnlyCollection<Result>.Empty);
        Assert.Equal("exclusivelyOwned", Assert.Throws<ArgumentNullException>(() => SafeReadOnlyCollection.Over<Result>(null!)).ParamName);
    }

    /// <summary>The view is a plain collection to every consumer: its type test, its debug text, and its size.</summary>
    [Fact]
    public void TheView_IsAReadOnlyCollection_WithItsText_AndNoFieldOfItsOwn()
    {
        var view = SafeReadOnlyCollection.Over(FreshAtoms());
        Assert.IsAssignableFrom<ReadOnlyCollection<Result>>(view);
        Assert.Equal(Array.AsReadOnly(FreshAtoms()).ToString(), view.ToString());
        Assert.Equal("System.Collections.ObjectModel.ReadOnlyCollection`1[KatLang.Result]", view.ToString());

        const BindingFlags instanceFields = BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.DeclaredOnly;
        Assert.Empty(typeof(SafeReadOnlyCollection<Result>).GetFields(instanceFields));
        Assert.Empty(typeof(SharedPropertyParameterList).GetFields(instanceFields));
    }

    /// <summary>A wrapper over another view keeps its own stable <c>SyncRoot</c> (the shared member lists of FE-4b).</summary>
    [Fact]
    public void AViewOverAView_KeepsItsOwnStableSyncRoot()
    {
        var inner = SafeReadOnlyCollection.Over(FreshAtoms());
        var outer = SafeReadOnlyCollection.OverList(inner);
        var other = SafeReadOnlyCollection.OverList(inner);

        Assert.Same(outer, ((ICollection)outer).SyncRoot);
        Assert.Same(other, ((ICollection)other).SyncRoot);
        Assert.NotSame(((ICollection)outer).SyncRoot, ((ICollection)other).SyncRoot);
        Assert.NotSame(inner, ((ICollection)outer).SyncRoot);
        Assert.Equal(Atoms, outer);
    }

    /// <summary>The one subclass, FE-3's shared parameter list, inherits the remap over an array and over a concatenation.</summary>
    [Fact]
    public void SharedPropertyParameterList_InheritsTheRemap()
    {
        PropertyParameterInfo[] parameters =
        [
            new("a", PropertyParameterKind.Explicit, null),
            new("b", PropertyParameterKind.Implicit, null),
        ];
        var shared = new SharedPropertyParameterList(parameters);
        var concatenated = SharedPropertyParameterList.Concat([new("head", PropertyParameterKind.Explicit, null)], shared);

        foreach (var list in new[] { shared, concatenated })
        {
            Assert.Same(list, ((ICollection)list).SyncRoot);
            Assert.Equal(typeof(SharedPropertyParameterList).ToString(), list.ToString());
            Assert.IsAssignableFrom<ReadOnlyCollection<PropertyParameterInfo>>(list);
            Assert.Throws<NotSupportedException>(() => ((IList<PropertyParameterInfo>)list).Clear());
        }

        Assert.Equal(["head", "a", "b"], concatenated.Select(static parameter => parameter.Name));
    }

    /// <summary>Values publish this view: construction snapshots, ownership transfer wraps the given array.</summary>
    [Fact]
    public void Values_PublishTheSafeView_OverTheirOwnArray()
    {
        var owned = FreshAtoms();
        var list = Result.ListValue.TakeOwnership(owned);
        var sequence = Result.SequenceValue.TakeOwnership(FreshAtoms());
        Assert.IsType<SafeReadOnlyCollection<Result>>(list.Items);
        Assert.IsType<SafeReadOnlyCollection<Result>>(sequence.Items);

        // Deliberately breaking the ownership rule to SEE the storage: no copy was made.
        owned[0] = Atoms[2];
        Assert.Same(Atoms[2], list.Items[0]);

        var snapshot = FreshAtoms();
        var built = new Result.ListValue(snapshot);
        snapshot[0] = Atoms[2];
        Assert.Same(Atoms[0], built.Items[0]);
        Assert.IsType<SafeReadOnlyCollection<Result>>(built.Items);

        Assert.Same(SafeReadOnlyCollection<Result>.Empty, Result.ListValue.TakeOwnership([]).Items);
        Assert.Same(SafeReadOnlyCollection<Result>.Empty, new Result.SequenceValue([]).Items);
    }

    /// <summary>
    /// No other type in the assembly derives from the plain collection: a second subclass would
    /// publish the base's <c>SyncRoot</c> again.
    /// </summary>
    [Fact]
    public void EveryReadOnlyCollectionSubclass_DerivesFromTheSafeView()
    {
        var offenders = typeof(KatLangEngine).Assembly.GetTypes()
            .Where(static type => IsOrDerivesFrom(type.BaseType, typeof(ReadOnlyCollection<>)))
            .Where(static type => !IsOrDerivesFrom(type, typeof(SafeReadOnlyCollection<>)))
            .Select(static type => type.FullName)
            .ToList();
        Assert.Empty(offenders);

        static bool IsOrDerivesFrom(Type? type, Type definition)
        {
            for (; type is not null; type = type.BaseType)
            {
                if (type.IsGenericType && type.GetGenericTypeDefinition() == definition)
                    return true;
            }

            return false;
        }
    }
}
