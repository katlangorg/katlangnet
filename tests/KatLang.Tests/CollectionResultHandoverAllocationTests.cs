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
    public void OrderResults_AllocateTheSortKeysTheNumbersAndOneExactArray_GcIsolatedChild()
    {
        if (!GcIsolatedAllocation.EnterChild())
            return;

        // Per item: one sort key, one new number and one result slot — no numeric list, no sorted copy,
        // no second result array.
        var keyType = typeof((Decimal128 Value, int Index));
        var expected = ArrayBytes(keyType, Large) - ArrayBytes(keyType, Small)
            + ((Large - Small) * ObjectBytes(typeof(Result.Atom)))
            + ResultArrayDelta(Small, Large);
        foreach (var builtin in new[] { BuiltinId.order, BuiltinId.orderDesc })
            Assert.Equal(expected, CallBytes(builtin, Args(Permuted(Large))) - CallBytes(builtin, Args(Permuted(Small))));
        GcIsolatedAllocation.Complete();
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
    /// <c>atoms</c>: the collected numbers are the traversal's own cost, measured by the same traversal;
    /// beyond it, one new number per atom and one exact array.
    /// </summary>
    [Fact]
    public void Atoms_AllocatesItsTraversalTheNumbersAndOneExactArray_GcIsolatedChild()
    {
        if (!GcIsolatedAllocation.EnterChild())
            return;

        var small = ListOf(Enumerable.Range(1, Small));
        var large = ListOf(Enumerable.Range(1, Large));
        var expected = TraversalBytes(large) - TraversalBytes(small)
            + ((Large - Small) * ObjectBytes(typeof(Result.Atom)))
            + ResultArrayDelta(Small, Large);
        Assert.Equal(expected, CallBytes(BuiltinId.atoms, Args(large)) - CallBytes(BuiltinId.atoms, Args(small)));
        GcIsolatedAllocation.Complete();
    }

    private static long TraversalBytes(Result value)
    {
        void Traverse(EvaluationBudget budget)
        {
            Assert.True(value.TryLanguageAtomsObserved(budget.MaxCollectionItems, null, out var atoms, budget));
            GC.KeepAlive(atoms);
        }

        Traverse(EvaluationBudget.Create(null));
        var budget = EvaluationBudget.Create(null);
        return Bytes(() => Traverse(budget));
    }
}
