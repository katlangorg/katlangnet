using System.Collections;
using System.Numerics;
using KatLang.Tests.Formatting;

namespace KatLang.Tests.RootOutputRowCounts;

/// <summary>
/// <see cref="RunResult.Success.OutputRowCounts"/> is ancillary host data, not part of a result's
/// identity: two successes that differ only in their partition are equal, hash alike and print
/// alike, the hash and the printed form are the ones the record had before the member existed,
/// the deconstruction still yields three values, copies share the view, and the view never hands
/// out its storage. The constructor refuses a partition that does not describe the result, and
/// the engine's projection from recorded slot counts keeps the sum by construction.
/// </summary>
public class OutputRowCountsRecordContractTests
{
    private const int HashFactor = -1521134295;

    /// <summary>
    /// Successes over ONE root of two spread rows, one value of three items, one atom list and one
    /// emitted count, differing only in how the three output rows are split between the two rows.
    /// </summary>
    private static RunResult.Success[] SamePayloadDifferentPartitions()
    {
        var spread = new Expr.SequenceSpread(HandBuiltSuccess.FixtureCall());
        var root = new Algorithm.User(null, [], [], [], [spread, spread]);
        Result value = new Result.SequenceValue([new Result.Atom(1), new Result.Atom(2), new Result.Atom(3)]);
        IReadOnlyList<Decimal128> atoms = new Decimal128[] { 1, 2, 3 };

        return
        [
            new RunResult.Success(root, value, atoms, EmittedCount: 3, OutputRowCounts: [1, 2]),
            new RunResult.Success(root, value, atoms, EmittedCount: 3, OutputRowCounts: [2, 1]),
            new RunResult.Success(root, value, atoms, EmittedCount: 3, OutputRowCounts: [3, 0]),
            new RunResult.Success(root, value, atoms, EmittedCount: 3, OutputRowCounts: [0, 3]),
        ];
    }

    [Fact]
    public void Partition_TakesNoPartInEquality()
    {
        var successes = SamePayloadDifferentPartitions();
        Assert.Equal(new[] { 1, 2 }, successes[0].OutputRowCounts);
        Assert.Equal(new[] { 0, 3 }, successes[3].OutputRowCounts);

        foreach (var other in successes)
        {
            Assert.True(successes[0].Equals(other));
            Assert.True(successes[0] == other);
            Assert.True(successes[0].Equals((RunResult)other));
            Assert.True(successes[0].Equals((object)other));
            Assert.Equal(successes[0].GetHashCode(), other.GetHashCode());
            Assert.Equal(successes[0].ToString(), other.ToString());
        }

        // The structural fields still decide: another emitted count is another result.
        var root = successes[0].Root;
        var oneRow = new RunResult.Success(root, successes[0].Value, successes[0].Atoms, EmittedCount: 1, OutputRowCounts: [1, 0]);
        Assert.False(successes[0].Equals(oneRow));
    }

    [Fact]
    public void Hash_IsTheCombinationTheRecordHadBeforeTheMember()
    {
        foreach (var success in SamePayloadDifferentPartitions().Append(EngineSuccess()))
        {
            // The synthesized record hash, written out: the base combines its equality contract,
            // its display options and its property-observation slot (which hashes to zero); the
            // variant then combines Root, Value, Atoms and the emitted count, in that order.
            // There is no step for the partition.
            var expected = EqualityComparer<Type>.Default.GetHashCode(typeof(RunResult.Success));
            unchecked
            {
                expected = expected * HashFactor + EqualityComparer<DisplayOptions>.Default.GetHashCode(success.DisplayOptions);
                expected = expected * HashFactor + 0;
                expected = expected * HashFactor + EqualityComparer<Algorithm.User>.Default.GetHashCode(success.Root);
                expected = expected * HashFactor + EqualityComparer<Result>.Default.GetHashCode(success.Value);
                expected = expected * HashFactor + EqualityComparer<IReadOnlyList<Decimal128>>.Default.GetHashCode(success.Atoms);
                expected = expected * HashFactor + EqualityComparer<int>.Default.GetHashCode(success.EmittedCount);
            }

            Assert.Equal(expected, success.GetHashCode());
        }
    }

    [Fact]
    public void Printing_KeepsTheExistingMembersInOrder_WithoutThePartition()
    {
        foreach (var success in SamePayloadDifferentPartitions().Append(EngineSuccess()))
        {
            var text = success.ToString();

            Assert.Equal(
                "Success { IsSuccess = True, IsNoProgramOutput = False, IsFailure = False"
                + $", Root = {success.Root}, Value = {success.Value}, Atoms = {success.Atoms}, OutputRows = {success.OutputRows} }}",
                text);
            Assert.DoesNotContain(nameof(RunResult.Success.OutputRowCounts), text, StringComparison.Ordinal);
        }
    }

    [Fact]
    public void Deconstruction_StillYieldsRootValueAndAtoms()
    {
        var success = EngineSuccess();

        var (root, value, atoms) = success;

        Assert.Same(success.Root, root);
        Assert.Same(success.Value, value);
        Assert.Same(success.Atoms, atoms);
        Assert.Equal(3, typeof(RunResult.Success).GetMethod(nameof(RunResult.Success.Deconstruct))!.GetParameters().Length);
        Assert.Single(typeof(RunResult.Success).GetMethods(), static method => method.Name == nameof(RunResult.Success.Deconstruct));
    }

    [Fact]
    public void Copies_ShareTheView_AndStayEqual()
    {
        var success = EngineSuccess();

        var copy = success with { };
        var reapplied = Assert.IsType<RunResult.Success>(success.WithHostDecimalPlaces(null, 3));
        var observed = success with { PropertyObservations = PropertyObservations.Empty };

        Assert.Same(success.OutputRowCounts, copy.OutputRowCounts);
        Assert.Same(success.OutputRowCounts, reapplied.OutputRowCounts);
        Assert.Same(success.OutputRowCounts, observed.OutputRowCounts);
        Assert.Equal(success, copy);
        Assert.Equal(success.GetHashCode(), copy.GetHashCode());
        Assert.Equal(success, observed);
        // Host settings are part of the result's display configuration, and so of its identity.
        Assert.NotEqual(success, reapplied);
    }

    [Fact]
    public void View_IsReadOnly_AndNeverHandsOutItsStorage()
    {
        foreach (var success in SamePayloadDifferentPartitions().Append(EngineSuccess()))
        {
            var counts = success.OutputRowCounts;
            var before = counts.ToArray();

            Assert.Same(counts, success.OutputRowCounts);
            Assert.False(counts is int[]);
            Assert.False(counts is List<int>);

            var writable = Assert.IsAssignableFrom<IList<int>>(counts);
            Assert.True(writable.IsReadOnly);
            Assert.Throws<NotSupportedException>(() => writable[0] = 99);
            Assert.Throws<NotSupportedException>(() => writable.Add(99));
            Assert.Throws<NotSupportedException>(writable.Clear);

            var untyped = Assert.IsAssignableFrom<IList>(counts);
            Assert.True(untyped.IsReadOnly);
            Assert.True(untyped.IsFixedSize);
            Assert.Throws<NotSupportedException>(() => untyped[0] = 99);

            // The non-generic SyncRoot of a plain read-only collection is its array; this view's is itself.
            var root = ((ICollection)counts).SyncRoot;
            Assert.Same(counts, root);
            Assert.False(root is Array);
            Assert.Same(root, ((ICollection)counts).SyncRoot);

            Assert.Equal(before, success.OutputRowCounts);
        }
    }

    [Fact]
    public void Constructor_RefusesAPartitionThatDoesNotDescribeTheResult()
    {
        var spread = new Expr.SequenceSpread(HandBuiltSuccess.FixtureCall());
        var twoRows = new Algorithm.User(null, [], [], [], [spread, spread]);
        var noRows = new Algorithm.User(null, [], [], [], []);
        Result three = new Result.SequenceValue([new Result.Atom(1), new Result.Atom(2), new Result.Atom(3)]);

        // One entry per root row.
        Assert.Throws<ArgumentException>(() => new RunResult.Success(twoRows, three, [], EmittedCount: 3, OutputRowCounts: [3]));
        Assert.Throws<ArgumentException>(() => new RunResult.Success(twoRows, three, [], EmittedCount: 3, OutputRowCounts: [1, 1, 1]));
        // A root without output rows cannot own a visible value: there is no empty fallback.
        Assert.Throws<ArgumentException>(() => new RunResult.Success(noRows, new Result.Atom(7), [], EmittedCount: 1, OutputRowCounts: []));
        // No negative entry, even when the sum would fit.
        Assert.Throws<ArgumentException>(() => new RunResult.Success(twoRows, three, [], EmittedCount: 3, OutputRowCounts: [4, -1]));
        // The entries sum to the presented output rows: three items, one whole value, or none.
        Assert.Throws<ArgumentException>(() => new RunResult.Success(twoRows, three, [], EmittedCount: 3, OutputRowCounts: [1, 1]));
        Assert.Throws<ArgumentException>(() => new RunResult.Success(twoRows, three, [], EmittedCount: 1, OutputRowCounts: [1, 2]));
        Assert.Throws<ArgumentException>(() => new RunResult.Success(twoRows, three, [], EmittedCount: 0, OutputRowCounts: [0, 1]));
        Assert.Throws<ArgumentNullException>(() => new RunResult.Success(twoRows, three, [], EmittedCount: 3, OutputRowCounts: null!));

        // The coherent forms of the same payload.
        Assert.Equal(3, new RunResult.Success(twoRows, three, [], EmittedCount: 3, OutputRowCounts: [1, 2]).OutputRows.Count);
        Assert.Single(new RunResult.Success(twoRows, three, [], EmittedCount: 1, OutputRowCounts: [0, 1]).OutputRows);
        Assert.Empty(new RunResult.Success(twoRows, three, [], EmittedCount: 0, OutputRowCounts: [0, 0]).OutputRows);
        Assert.Empty(new RunResult.Success(noRows, new Result.SequenceValue([]), [], EmittedCount: 0, OutputRowCounts: []).OutputRowCounts);
    }

    [Fact]
    public void HandBuiltFixtures_AreCoherent()
    {
        var plain = HandBuiltSuccess.OfOnePlainRow(new Result.SequenceValue([new Result.Atom(1), new Result.Atom(2)]));
        OutputRowCountsTestSupport.AssertPartition(plain);
        Assert.Equal(new[] { 1 }, plain.OutputRowCounts);
        Assert.Single(plain.OutputRows);

        var spread = HandBuiltSuccess.OfOneSpreadRow(new Result.SequenceValue([new Result.Atom(1), new Result.Atom(2)]), emittedCount: 2);
        OutputRowCountsTestSupport.AssertPartition(spread);
        Assert.Equal(new[] { 2 }, spread.OutputRowCounts);

        var none = HandBuiltSuccess.OfOneSpreadRow(new Result.SequenceValue([]), emittedCount: 0);
        OutputRowCountsTestSupport.AssertPartition(none);
        Assert.Equal(new[] { 0 }, none.OutputRowCounts);
    }

    // ── The engine's projection from recorded slot counts ───────────────────

    private static Evaluator.CountedResult Counted(Result value, int emittedCount) => new(value, emittedCount);

    private static Result Sequence(params int[] numbers)
        => new Result.SequenceValue(numbers.Select(static n => (Result)new Result.Atom(n)).ToArray());

    [Fact]
    public void Projection_KeepsEachSlotsOwner_WhenEverySlotIsOneOutputRow()
    {
        // No slot, no row.
        Assert.Equal(new[] { 0, 0 }, KatLangEngine.ProjectOutputRowCounts([0, 0], 2, Counted(new Result.SequenceValue([]), 0)));
        // One slot, the one value: also when that value is itself a sequence or a list.
        Assert.Equal(new[] { 0, 1, 0 }, KatLangEngine.ProjectOutputRowCounts([0, 1, 0], 3, Counted(new Result.Atom(5), 1)));
        Assert.Equal(new[] { 0, 1, 0 }, KatLangEngine.ProjectOutputRowCounts([0, 1, 0], 3, Counted(Sequence(1, 2, 3), 1)));
        Assert.Equal(new[] { 1 }, KatLangEngine.ProjectOutputRowCounts([1], 1, Counted(new Result.ListValue([new Result.Atom(1), new Result.Atom(2)]), 1)));
        // Several slots: the value is their sequence, and each keeps its recorded owner.
        Assert.Equal(new[] { 2, 0, 1, 3 }, KatLangEngine.ProjectOutputRowCounts([2, 0, 1, 3], 4, Counted(Sequence(1, 2, 3, 4, 5, 6), 6)));
        // An emitted count that is larger than the slot count still presents the stored items.
        Assert.Equal(new[] { 2, 1 }, KatLangEngine.ProjectOutputRowCounts([2, 1], 2, Counted(Sequence(1, 2, 3), 7)));
    }

    [Fact]
    public void Projection_GivesASoleSlotsSeveralRows_ToTheRowThatSuppliedIt_AndKeepsTheZerosAroundIt()
    {
        // The row loop passes a sole slot through as the value itself, and the many rule of the
        // output rows then presents that value's own items: all of them belong to the one row.
        var value = Sequence(1, 2, 3);
        var counts = KatLangEngine.ProjectOutputRowCounts([0, 1, 0], 3, Counted(value, 3));

        Assert.Equal(new[] { 0, 3, 0 }, counts);
        Assert.Equal(RunResult.RowCountOf(value, 3), counts.Sum());

        // The partition then describes the result: the success constructor accepts it.
        var spread = new Expr.SequenceSpread(HandBuiltSuccess.FixtureCall());
        var root = new Algorithm.User(null, [], [], [], [spread, spread, spread]);
        var success = new RunResult.Success(root, value, [], EmittedCount: 3, counts);
        OutputRowCountsTestSupport.AssertPartition(success);
        Assert.Equal(3, success.OutputRows.Count);

        // A sole slot whose value has no items to open is one row under the many rule too.
        Assert.Equal(new[] { 1, 0 }, KatLangEngine.ProjectOutputRowCounts([1, 0], 2, Counted(new Result.Atom(5), 4)));
        Assert.Equal(new[] { 1, 0 }, KatLangEngine.ProjectOutputRowCounts(
            [1, 0], 2, Counted(new Result.ListValue([new Result.Atom(1), new Result.Atom(2)]), 2)));
    }

    [Fact]
    public void Projection_FailsLoudly_ForCountsTheRowLoopCannotProduce()
    {
        // Nothing recorded, or recorded for another row count.
        Assert.Throws<InvalidOperationException>(() => KatLangEngine.ProjectOutputRowCounts(null, 1, Counted(new Result.Atom(5), 1)));
        Assert.Throws<InvalidOperationException>(() => KatLangEngine.ProjectOutputRowCounts([1], 2, Counted(new Result.Atom(5), 1)));
        // No slot presented as one row, and several slots presented as one row or none.
        Assert.Throws<InvalidOperationException>(() => KatLangEngine.ProjectOutputRowCounts([0, 0], 2, Counted(new Result.SequenceValue([]), 1)));
        Assert.Throws<InvalidOperationException>(() => KatLangEngine.ProjectOutputRowCounts([1, 1], 2, Counted(Sequence(1, 2), 1)));
        Assert.Throws<InvalidOperationException>(() => KatLangEngine.ProjectOutputRowCounts([1, 1], 2, Counted(Sequence(1, 2), 0)));
    }

    [Fact]
    public void RowCountOf_IsTheLengthOfTheOutputRows()
    {
        (Result Value, int EmittedCount)[] cases =
        [
            (new Result.SequenceValue([]), 0),
            (new Result.Atom(5), 1),
            (Sequence(1, 2, 3), 1),
            (Sequence(1, 2, 3), 3),
            (new Result.Atom(5), 2),
            (new Result.ListValue([new Result.Atom(1), new Result.Atom(2)]), 2),
            (new Result.Str(""), 1),
        ];

        foreach (var (value, emittedCount) in cases)
        {
            var success = HandBuiltSuccess.OfOneSpreadRow(value, emittedCount);
            Assert.Equal(success.OutputRows.Count, RunResult.RowCountOf(value, emittedCount));
        }
    }

    private static RunResult.Success EngineSuccess()
        => Assert.IsType<RunResult.Success>(KatLangEngine.Run(
            "Six(x)* = x, x + 1, x + 2, x + 3, x + 4, x + 5\nSix(10)\n''\nSix(20)"));
}
