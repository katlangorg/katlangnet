using System.Numerics;
using System.Reflection;
using KatLang.Evaluation;
using KatLang.TestInfrastructure;

namespace KatLang.Tests;

/// <summary>
/// Collection-builtin result hand-over and numeric views (2026-11-17; an implementation-only
/// optimization). <c>take</c>, <c>skip</c>, <c>distinct</c>, <c>order</c>, <c>orderDesc</c> and
/// <c>atoms</c> reserve their exact result count and fill ONE exactly sized array that becomes the list,
/// instead of building a list that <c>MakeCollectionListResult</c> copied again; <c>sum</c>, <c>avg</c>,
/// <c>min</c>, <c>max</c>, <c>order</c> and <c>orderDesc</c> read the validated items through a numeric
/// view instead of a copied <c>List&lt;Decimal128&gt;</c>. Each measurement compares the same builtin
/// application at two collection sizes, so the per-call scaffolding cancels and the difference is exactly
/// the per-item allocation: one result array (plus the sort keys and the new numbers of <c>order</c>, the
/// first-occurrence bit set and the set of <c>distinct</c>, the traversal of <c>atoms</c>), and nothing at
/// all for the numeric reducers. Before the change every list builder paid a second result array and
/// every numeric builtin a <c>Decimal128</c> array, so each assertion fails there. Strict counts run in
/// the isolated child process (<see cref="GcIsolatedAllocation"/>); the values and errors of these
/// builtins are pinned by their ordinary suites.
/// <para>The large-object follow-ups (2026-11-18, implementation-only) tightened five of these: <c>order</c>
/// sorts 4-byte input positions instead of 32-byte <c>(Decimal128, int)</c> keys, <c>atoms</c> reads a flat numeric prefix from its immutable input instead of collecting a doubling <c>Decimal128</c> list, <c>distinct</c> grows its set in small pages, the retained-collector <c>take</c> fills
/// its exact array instead of a list it then copied, and the fused filter→count reads a dotted receiver's
/// items through the generic view instead of copying them. Each assertion below fails on the code before
/// that change.</para>
/// </summary>
public class CollectionResultHandoverAllocationTests
{
    private delegate EvalResult<Evaluator.CountedResult> ApplyResolved(
        BuiltinId builtin, IReadOnlyList<Evaluator.ResolvedArgumentAlgorithm> resolvedArgs, Evaluator.EvalCtx ctx,
        IReadOnlyList<(string Name, Result Value)> valEnv);

    private static readonly ApplyResolved Apply =
        typeof(Evaluator).GetMethod("ApplyBuiltinCountedResolved", BindingFlags.NonPublic | BindingFlags.Static)!
            .CreateDelegate<ApplyResolved>();

    private const int Small = 1_000;
    private const int Large = 3_000;

    private static Result ListOf(IEnumerable<int> values)
        => new Result.ListValue(values.Select(static value => (Result)new Result.Atom(value)));

    // A permutation of 1..n (7919 is prime and does not divide either size): unordered, all distinct.
    private static Result Permuted(int n)
        => ListOf(Enumerable.Range(0, n).Select(i => (int)((i * 7919L) % n) + 1));

    private static Evaluator.ResolvedArgumentAlgorithm Supplied(Result value)
        => new(null) { Cell = NeedCell.Ready(new(value, value.ValueCount())) };

    private static Evaluator.ResolvedArgumentAlgorithm[] Args(Result collection, int? control = null)
        => control is { } count ? [Supplied(collection), Supplied(new Result.Atom(count))] : [Supplied(collection)];

    private static long Bytes(Action action)
    {
        var before = GC.GetAllocatedBytesForCurrentThread();
        action();
        return GC.GetAllocatedBytesForCurrentThread() - before;
    }

    private static long ArrayBytes(Type elementType, int length)
    {
        var arrayType = elementType.MakeArrayType();
        _ = Array.CreateInstanceFromArrayType(arrayType, length);
        return Bytes(() => _ = Array.CreateInstanceFromArrayType(arrayType, length));
    }

    private static long ObjectBytes(Type type)
    {
        _ = System.Runtime.CompilerServices.RuntimeHelpers.GetUninitializedObject(type);
        return Bytes(() => _ = System.Runtime.CompilerServices.RuntimeHelpers.GetUninitializedObject(type));
    }

    private static long ResultArrayDelta(int smaller, int larger)
        => ArrayBytes(typeof(Result), larger) - ArrayBytes(typeof(Result), smaller);

    /// <summary>The bytes one successful application allocates (warmed first; its context is created outside the window).</summary>
    private static long CallBytes(BuiltinId builtin, Evaluator.ResolvedArgumentAlgorithm[] args)
    {
        IReadOnlyList<(string Name, Result Value)> values = [];
        var warm = Apply(builtin, args, Evaluator.EvalCtx.Empty, values);
        Assert.True(warm.IsOk, warm.IsError ? warm.Error.ToString() : null);

        var ctx = Evaluator.EvalCtx.Empty;
        EvalResult<Evaluator.CountedResult> result = default;
        var bytes = Bytes(() => result = Apply(builtin, args, ctx, values));
        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : null);
        GC.KeepAlive(result);
        return bytes;
    }

    [Fact]
    public void SliceResults_AllocateOneExactArray_GcIsolatedChild()
    {
        if (!GcIsolatedAllocation.EnterChild())
            return;

        // A prefix or suffix of 1,000 / 2,000 items (copied item by item) and the whole 3,000 (copied in bulk).
        var source = ListOf(Enumerable.Range(1, Large));
        Assert.Equal(
            ResultArrayDelta(Small, 2 * Small),
            CallBytes(BuiltinId.take, Args(source, 2 * Small)) - CallBytes(BuiltinId.take, Args(source, Small)));
        Assert.Equal(
            ResultArrayDelta(Small, Large),
            CallBytes(BuiltinId.take, Args(source, Large)) - CallBytes(BuiltinId.take, Args(source, Small)));
        Assert.Equal(
            ResultArrayDelta(Small, 2 * Small),
            CallBytes(BuiltinId.skip, Args(source, Small)) - CallBytes(BuiltinId.skip, Args(source, 2 * Small)));
        Assert.Equal(
            ResultArrayDelta(Small, Large),
            CallBytes(BuiltinId.skip, Args(source, 0)) - CallBytes(BuiltinId.skip, Args(source, 2 * Small)));
        GcIsolatedAllocation.Complete();
    }

    [Fact]
    public void OrderResults_AllocateThePositionsTheNumbersAndOneExactArray_GcIsolatedChild()
    {
        if (!GcIsolatedAllocation.EnterChild())
            return;

        // Per item: one sorted input position (4 bytes), one new number and one result slot — no
        // 32-byte (value, index) sort key, no numeric list, no sorted copy, no second result array.
        var expected = ArrayBytes(typeof(int), Large) - ArrayBytes(typeof(int), Small)
            + ((Large - Small) * ObjectBytes(typeof(Result.Atom)))
            + ResultArrayDelta(Small, Large);
        foreach (var builtin in new[] { BuiltinId.order, BuiltinId.orderDesc })
            Assert.Equal(expected, CallBytes(builtin, Args(Permuted(Large))) - CallBytes(builtin, Args(Permuted(Small))));
        GcIsolatedAllocation.Complete();
    }

    // Cancel on the first inspected sort value, deterministically between binding and reservation.
    // A reservation moved ahead of sorting would charge the list and miss this cancellation.
    private sealed class CancelOnSortRead(CancellationTokenSource source) : IReadOnlyList<Result>
    {
        public int Count => 3;

        public Result this[int index]
        {
            get
            {
                source.Cancel();
                return new Result.Atom(Count - index);
            }
        }

        public IEnumerator<Result> GetEnumerator() => throw new NotSupportedException();
        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void Order_CancellationDuringSortPrecedesResultReservation(bool descending)
    {
        using var cancellation = new CancellationTokenSource();
        var budget = EvaluationBudget.Create(null, cancellationToken: cancellation.Token);
        var ctx = Evaluator.EvalCtx.Empty with { Budget = budget };
        var viewType = typeof(Evaluator).GetNestedType("SingleAtomicNumberItems", BindingFlags.NonPublic)!;
        var numbers = Activator.CreateInstance(viewType, new CancelOnSortRead(cancellation));
        var sort = typeof(Evaluator).GetMethod("MakeSortedNumberListResult", BindingFlags.NonPublic | BindingFlags.Static)!;

        var failure = Assert.Throws<TargetInvocationException>(() => sort.Invoke(null, [ctx, numbers, descending]));
        Assert.Equal(cancellation.Token, Assert.IsType<OperationCanceledException>(failure.InnerException).CancellationToken);
        Assert.Equal(0, budget.MaterializedItems);
    }

    [Fact]
    public void NumericReducers_AllocateNothingPerItem_GcIsolatedChild()
    {
        if (!GcIsolatedAllocation.EnterChild())
            return;

        foreach (var builtin in new[] { BuiltinId.sum, BuiltinId.avg, BuiltinId.min, BuiltinId.max })
            Assert.Equal(CallBytes(builtin, Args(Permuted(Small))), CallBytes(builtin, Args(Permuted(Large))));
        GcIsolatedAllocation.Complete();
    }

    /// <summary>
    /// <c>distinct</c>: the first-occurrence set is the operation comparer's own cost, measured by the same
    /// set filled with the same comparer over the same items; beyond it, one bit set and one exact array.
    /// </summary>
    [Fact]
    public void Distinct_AllocatesItsSetOneBitSetAndOneExactArray_GcIsolatedChild()
    {
        if (!GcIsolatedAllocation.EnterChild())
            return;

        // All distinct, and every item twice (half of them kept).
        foreach (var repeat in new[] { 1, 2 })
        {
            Result Source(int n) => ListOf(Enumerable.Range(0, n).Select(i => (i % (n / repeat)) + 1));
            var small = Source(Small);
            var large = Source(Large);
            var expected = SetBytes(large) - SetBytes(small)
                + ArrayBytes(typeof(ulong), (Large + 63) / 64) - ArrayBytes(typeof(ulong), (Small + 63) / 64)
                + ResultArrayDelta(Small / repeat, Large / repeat);
            Assert.Equal(expected, CallBytes(BuiltinId.distinct, Args(large)) - CallBytes(BuiltinId.distinct, Args(small)));
        }

        GcIsolatedAllocation.Complete();
    }

    /// <summary>
    /// <c>atoms</c> of a flat list: the walk reuses the input prefix. After reservation the builtin makes one new
    /// number per atom in the exact array that becomes the list — no collected <c>Decimal128</c> list beside them.
    /// </summary>
    [Fact]
    public void Atoms_OfAFlatList_AllocatesTheNumbersAndOneExactArray_GcIsolatedChild()
    {
        if (!GcIsolatedAllocation.EnterChild())
            return;

        var small = ListOf(Enumerable.Range(1, Small));
        var large = ListOf(Enumerable.Range(1, Large));
        var expected = ((Large - Small) * ObjectBytes(typeof(Result.Atom))) + ResultArrayDelta(Small, Large);
        Assert.Equal(expected, CallBytes(BuiltinId.atoms, Args(large)) - CallBytes(BuiltinId.atoms, Args(small)));

        // Both lists produce a single atom. Their input widths must not size a result buffer.
        Result Sparse(int n) => new Result.ListValue(Enumerable.Repeat<Result>(new Result.Str("x"), n - 1)
            .Append(new Result.Atom(7)));
        Assert.Equal(CallBytes(BuiltinId.atoms, Args(Sparse(Small))), CallBytes(BuiltinId.atoms, Args(Sparse(Large))));

        // A refused final reservation may traverse the flat input, but constructs no per-item output.
        long RefusedBytes(Result source)
        {
            var args = Args(source);
            var budget = EvaluationBudget.Create(new EvaluationLimits { MaxMaterializedItems = 1 });
            var ctx = Evaluator.EvalCtx.Empty with { Budget = budget };
            EvalResult<Evaluator.CountedResult> result = default;
            var bytes = Bytes(() => result = Apply(BuiltinId.atoms, args, ctx, []));
            Assert.IsType<EvalError.MaterializationLimitExceeded>(result.Error);
            Assert.Equal(0, budget.MaterializedItems);
            return bytes;
        }
        _ = RefusedBytes(small);
        Assert.Equal(RefusedBytes(small), RefusedBytes(large));
        GcIsolatedAllocation.Complete();
    }

    /// <summary>
    /// At 100k inputs the bit set costs one bit per input and the exact result eight bytes per
    /// first occurrence on x64. Allow the paged set two 16-byte slots per first occurrence and
    /// 32 KiB for small capacities, array headers, the directory and dispatch. Repeats after
    /// a full page or full table must not cause a reservation for every remaining input.
    /// </summary>
    [Fact]
    public void Distinct_LargeInput_AllocatesWithTheNumberOfFirstOccurrences_GcIsolatedChild()
    {
        if (!GcIsolatedAllocation.EnterChild())
            return;

        const int count = 100_000;
        foreach (var unique in new[] { 100, 4_049, 4_096, 5_000, count })
        {
            var source = ListOf(Enumerable.Range(0, count).Select(i => i % unique));
            var bound = ArrayBytes(typeof(ulong), (count + 63) / 64) + ArrayBytes(typeof(Result), unique)
                + 32L * unique + 32 * 1024;
            var actual = CallBytes(BuiltinId.distinct, Args(source));
            Assert.True(actual <= bound, $"{unique} distinct values: allocated {actual} bytes, bound {bound}.");
        }
        GcIsolatedAllocation.Complete();
    }

    private static long SetBytes(Result collection)
    {
        var items = ((Result.ListValue)collection).Items;
        void Fill(EvaluationBudget budget)
        {
            var comparer = Result.CreateOperationComparer(budget);
            var seen = new HashSet<Result>(comparer);
            for (var i = 0; i < items.Count; i++)
                seen.Add(items[i]);

            Assert.Null(comparer.CompleteOperation());
        }

        Fill(EvaluationBudget.Create(null));
        var budget = EvaluationBudget.Create(null);
        return Bytes(() => Fill(budget));
    }

    /// <summary>
    /// <c>take</c> observing a RETAINED collector (NEED-07) demands its prefix cells and fills the ONE exact
    /// array that becomes the list: the bytes of a longer prefix differ by exactly the longer array, where the
    /// former list of the prefix and its copy cost two.
    /// </summary>
    [Fact]
    public void RetainedTake_AllocatesOneExactArray_GcIsolatedChild()
    {
        if (!GcIsolatedAllocation.EnterChild())
            return;

        var cells = Enumerable.Range(1, Large).Select(static n => NeedCell.Ready(new(new Result.Atom(n), 1))).ToArray();
        var collector = new NeedCell(
            static () => throw new InvalidOperationException("take must not demand the collector's whole value"),
            static () => throw new InvalidOperationException("take must not demand the collector's whole value"),
            slice: cells);
        Evaluator.ResolvedArgumentAlgorithm[] Prefix(int count)
            => [new(null) { Cell = collector }, Supplied(new Result.Atom(count))];

        Assert.Equal(
            ResultArrayDelta(Small, 2 * Small),
            CallBytes(BuiltinId.take, Prefix(2 * Small)) - CallBytes(BuiltinId.take, Prefix(Small)));
        Assert.Equal(
            ResultArrayDelta(Small, Large),
            CallBytes(BuiltinId.take, Prefix(Large + 5)) - CallBytes(BuiltinId.take, Prefix(Small)));
        GcIsolatedAllocation.Complete();
    }

    private delegate EvalResult<IReadOnlyList<Evaluator.CountedResult>> ReceiverAdapter(
        Expr receiver, Evaluator.EvalCtx ctx, IReadOnlyList<(string Name, Result Value)> valEnv);

    private static readonly ReceiverAdapter DotReceiverItems =
        typeof(Evaluator).GetMethod("EvaluateDotReceiverIterationItemsForSequenceOptimizer", BindingFlags.NonPublic | BindingFlags.Static)!
            .CreateDelegate<ReceiverAdapter>();

    /// <summary>
    /// The fused filter→count's dot-receiver adapter reads a non-range receiver's items through the generic
    /// binding's own view — each item as stored, with emitted count 1 — and allocates nothing per item (it
    /// copied them into a list of counted items, 16 bytes each). The receiver is a parameter holding a
    /// prebuilt list, so nothing else scales with the list.
    /// </summary>
    [Fact]
    public void FusedDotReceiverItems_AllocateNothingPerItem_GcIsolatedChild()
    {
        if (!GcIsolatedAllocation.EnterChild())
            return;

        long AdapterBytes(int count)
        {
            var list = ListOf(Enumerable.Range(1, count));
            var ctx = Evaluator.LoopNeedBindingContext(Evaluator.EvalCtx.Empty, ["xs"], [NeedCell.Ready(new(list, 1))]);
            IReadOnlyList<(string Name, Result Value)> values = [];
            var receiver = new Expr.Param("xs");
            var warm = DotReceiverItems(receiver, ctx, values);
            Assert.True(warm.IsOk, warm.IsError ? warm.Error.ToString() : null);
            var expectedItems = ((Result.ListValue)list).Items;
            Assert.Equal(count, warm.Value.Count);
            for (var i = 0; i < count; i++)
            {
                Assert.Same(expectedItems[i], warm.Value[i].Value);
                Assert.Equal(1, warm.Value[i].EmittedCount);
            }

            EvalResult<IReadOnlyList<Evaluator.CountedResult>> result = default;
            var bytes = Bytes(() => result = DotReceiverItems(receiver, ctx, values));
            Assert.True(result.IsOk);
            GC.KeepAlive(result);
            return bytes;
        }

        Assert.Equal(AdapterBytes(Small), AdapterBytes(Large));
        GcIsolatedAllocation.Complete();
    }
}
