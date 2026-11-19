using System.Collections.ObjectModel;
using KatLang.TestInfrastructure;

namespace KatLang.Tests;

/// <summary>
/// A list or sequence value still costs the record and ONE view object over the array it was
/// given (November 2026, <see cref="SafeReadOnlyCollection{T}"/>): the view that no longer hands
/// out its storage adds no object, no field and no copy to the plain
/// <see cref="ReadOnlyCollection{T}"/> it replaced, and an empty value still allocates no view at
/// all. Strict counts, so they run in the isolated child process
/// (<see cref="GcIsolatedAllocation"/>).
/// </summary>
public class ReadOnlyViewAllocationTests
{
    /// <summary>The bytes the second run of <paramref name="action"/> allocates (the first run warms it).</summary>
    private static long Bytes(Action action)
    {
        action();
        var before = GC.GetAllocatedBytesForCurrentThread();
        action();
        return GC.GetAllocatedBytesForCurrentThread() - before;
    }

    private static long ObjectBytes(Type type)
        => Bytes(() => _ = System.Runtime.CompilerServices.RuntimeHelpers.GetUninitializedObject(type));

    [Fact]
    public void TakeOwnership_AllocatesTheValueAndOneViewOverTheGivenArray_GcIsolatedChild()
    {
        if (!GcIsolatedAllocation.EnterChild())
            return;

        // What the plain view cost before the change: one object holding one reference.
        var plainView = ObjectBytes(typeof(ReadOnlyCollection<Result>));
        Assert.Equal(plainView, ObjectBytes(typeof(SafeReadOnlyCollection<Result>)));
        ReadOnlyCollection<Result>? view = null;
        var plainItems = new Result[] { new Result.Atom(1), new Result.Atom(2), new Result.Atom(3) };
        Assert.Equal(plainView, Bytes(() => view = Array.AsReadOnly(plainItems)));
        Assert.Equal(plainView, Bytes(() => view = SafeReadOnlyCollection.Over(plainItems)));
        if (Environment.Is64BitProcess)
            Assert.Equal(24, plainView);

        var listItems = new Result[] { new Result.Atom(1), new Result.Atom(2), new Result.Atom(3) };
        var sequenceItems = new Result[] { new Result.Atom(4), new Result.Atom(5) };
        Result.ListValue? list = null;
        Result.SequenceValue? sequence = null;

        // The record and its one view; the array is the caller's, already allocated.
        Assert.Equal(
            ObjectBytes(typeof(Result.ListValue)) + plainView,
            Bytes(() => list = Result.ListValue.TakeOwnership(listItems)));
        Assert.Equal(
            ObjectBytes(typeof(Result.SequenceValue)) + plainView,
            Bytes(() => sequence = Result.SequenceValue.TakeOwnership(sequenceItems)));

        Result[]? snapshot = null;
        var arrayBytes = Bytes(() => snapshot = (Result[])listItems.Clone());
        Result.ListValue? hostList = null;
        Assert.Equal(ObjectBytes(typeof(Result.ListValue)) + plainView + arrayBytes,
            Bytes(() => hostList = new Result.ListValue(listItems)));
        GC.KeepAlive(snapshot);
        GC.KeepAlive(hostList);

        // No copy: the view reads the given array (seen by breaking the ownership rule on purpose).
        var planted = new Result.Atom(9);
        listItems[0] = planted;
        sequenceItems[1] = planted;
        Assert.Same(planted, list!.Items[0]);
        Assert.Same(planted, sequence!.Items[1]);

        // One view per value: reading it, indexing it and copying the record allocate no second view.
        var readList = list;
        var readSequence = sequence;
        long total = 0;
        Assert.Equal(0, Bytes(() =>
        {
            total += readList.Items.Count + readSequence.Items.Count;
            total += ReferenceEquals(readList.Items, readList.Items) ? 1 : 0;
            total += ReferenceEquals(readList.Items[1], readSequence.Items[0]) ? 1 : 0;
        }));
        Assert.Equal(12, total);
        Result.ListValue? copy = null;
        Assert.Equal(ObjectBytes(typeof(Result.ListValue)), Bytes(() => copy = readList with { }));
        Assert.Same(readList.Items, copy!.Items);

        // An empty value shares the one empty view: only the record is allocated.
        var none = Array.Empty<Result>();
        Assert.Equal(ObjectBytes(typeof(Result.ListValue)), Bytes(() => list = Result.ListValue.TakeOwnership(none)));
        Assert.Equal(ObjectBytes(typeof(Result.SequenceValue)), Bytes(() => sequence = Result.SequenceValue.TakeOwnership(none)));
        Assert.Same(list!.Items, sequence!.Items);

        GC.KeepAlive(view);
        GcIsolatedAllocation.Complete();
    }
}
