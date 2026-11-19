using System.Collections;
using System.Reflection;
using System.Runtime.ExceptionServices;

namespace KatLang.Formatting.PublicApi.Tests;

/// <summary>
/// What safe managed code can do to a collection KatLang published: cast it, read its non-generic
/// <see cref="ICollection.SyncRoot"/>, and call the mutation members of every collection interface
/// it implements. <see cref="AssertHandsOutNoStorage"/> fails when any of those reaches writable
/// storage. Reflection, <c>unsafe</c> code and the marshalling helpers are outside the guarantee
/// (<c>docs/design/language-rules/evaluator-and-hosting.md</c>, Read-only views never hand out
/// their storage), so nothing here uses them against the collection.
/// </summary>
internal static class PublishedCollection
{
    /// <summary>
    /// Fails when <paramref name="collection"/>, or the object its <c>SyncRoot</c> returns, is
    /// writable storage — a non-empty array, a <see cref="List{T}"/>, or any list or collection
    /// that does not report itself read-only — when <c>SyncRoot</c> is not one stable object, or
    /// when a mutation member does anything but throw <see cref="NotSupportedException"/>. The
    /// content must be the same objects in the same order afterwards.
    /// </summary>
    public static void AssertHandsOutNoStorage(object collection, string site)
    {
        ArgumentNullException.ThrowIfNull(collection);
        // A zero-length array has nothing to write: Array.Empty<T>() is a legitimate published list.
        if (collection is Array { Length: 0 })
            return;

        var before = Snapshot(collection);
        Assert.True(WritableStorageKind(collection) is null,
            $"{site}: the published object is {WritableStorageKind(collection)} ({Describe(collection)}).");

        if (collection is ICollection untyped)
        {
            var root = untyped.SyncRoot;
            Assert.True(ReferenceEquals(root, untyped.SyncRoot), $"{site}: SyncRoot is a different object on a second read.");
            Assert.True(root is not Array, $"{site}: SyncRoot is an array ({Describe(root)}); a cast makes it writable.");
            Assert.True(WritableStorageKind(root) is null,
                $"{site}: SyncRoot is {WritableStorageKind(root)} ({Describe(root)}).");
            Assert.False(untyped.IsSynchronized, $"{site}: IsSynchronized changed.");
        }

        AssertEveryMutationMemberThrows(collection, site, before);
        var after = Snapshot(collection);
        Assert.True(before.Length == after.Length && before.Zip(after).All(pair => ReferenceEquals(pair.First, pair.Second) || Equals(pair.First, pair.Second)),
            $"{site}: the content changed while its mutation members were called.");
    }

    /// <summary>
    /// What <see cref="AssertHandsOutNoStorage"/> would report for <paramref name="collection"/>,
    /// or null when it hands out no storage.
    /// </summary>
    public static string? FindStorage(object collection, string site)
    {
        try
        {
            AssertHandsOutNoStorage(collection, site);
            return null;
        }
        catch (Xunit.Sdk.XunitException failure)
        {
            return failure.Message;
        }
    }

    /// <summary>The kind of writable storage <paramref name="candidate"/> is, or null when it is none.</summary>
    public static string? WritableStorageKind(object? candidate)
    {
        switch (candidate)
        {
            case null:
                return null;
            case Array { Length: 0 }:
                return null;
            case Array:
                return "an array";
        }

        var type = candidate.GetType();
        if (type.IsGenericType && type.GetGenericTypeDefinition() == typeof(List<>))
            return "a List<T>";
        if (candidate is IList { IsReadOnly: false })
            return "a writable IList";
        foreach (var contract in GenericCollectionContracts(type))
        {
            if (!(bool)contract.GetProperty(nameof(ICollection<int>.IsReadOnly))!.GetValue(candidate)!)
                return $"a writable {contract.Name}";
        }

        return null;
    }

    private static void AssertEveryMutationMemberThrows(object collection, string site, object?[] content)
    {
        var item = content.Length > 0 ? content[0] : null;
        if (collection is IList untyped)
        {
            Assert.True(untyped.IsReadOnly, $"{site}: IList.IsReadOnly is false.");
            Refused(site, "IList.set_Item", () => untyped[0] = item);
            Refused(site, "IList.Add", () => untyped.Add(item));
            Refused(site, "IList.Insert", () => untyped.Insert(0, item));
            Refused(site, "IList.Remove", () => untyped.Remove(item));
            Refused(site, "IList.RemoveAt", () => untyped.RemoveAt(0));
            Refused(site, "IList.Clear", untyped.Clear);
        }

        foreach (var contract in GenericCollectionContracts(collection.GetType()))
        {
            var probe = typeof(PublishedCollection)
                .GetMethod(nameof(AssertGenericMutationMembersThrow), BindingFlags.NonPublic | BindingFlags.Static)!
                .MakeGenericMethod(contract.GetGenericArguments()[0]);
            try
            {
                probe.Invoke(null, [collection, site]);
            }
            catch (TargetInvocationException wrapped) when (wrapped.InnerException is not null)
            {
                ExceptionDispatchInfo.Capture(wrapped.InnerException).Throw();
            }
        }
    }

    private static void AssertGenericMutationMembersThrow<T>(ICollection<T> collection, string site)
    {
        Assert.True(collection.IsReadOnly, $"{site}: ICollection<{typeof(T).Name}>.IsReadOnly is false.");
        var item = collection.FirstOrDefault()!;
        Refused(site, "ICollection<T>.Add", () => collection.Add(item));
        Refused(site, "ICollection<T>.Remove", () => collection.Remove(item));
        Refused(site, "ICollection<T>.Clear", collection.Clear);
        if (collection is IList<T> list)
        {
            Refused(site, "IList<T>.set_Item", () => list[0] = item);
            Refused(site, "IList<T>.Insert", () => list.Insert(0, item));
            Refused(site, "IList<T>.RemoveAt", () => list.RemoveAt(0));
        }
    }

    private static void Refused(string site, string member, Action mutation)
    {
        try
        {
            mutation();
        }
        catch (NotSupportedException)
        {
            return;
        }
        catch (Exception other)
        {
            Assert.Fail($"{site}: {member} threw {other.GetType().Name}, not NotSupportedException.");
        }

        Assert.Fail($"{site}: {member} did not throw.");
    }

    /// <summary>The closed <see cref="ICollection{T}"/> contracts <paramref name="type"/> implements.</summary>
    private static IEnumerable<Type> GenericCollectionContracts(Type type)
        => type.GetInterfaces().Where(contract => contract.IsGenericType && contract.GetGenericTypeDefinition() == typeof(ICollection<>));

    public static object?[] Snapshot(object collection)
        => [.. ((IEnumerable)collection).Cast<object?>()];

    public static string Describe(object? value)
        => value is null ? "null" : value.GetType().ToString();
}
