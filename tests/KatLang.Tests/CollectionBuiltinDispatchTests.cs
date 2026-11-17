using System.Collections;
using System.Numerics;
using System.Reflection;
using KatLang.Evaluation;
using KatLang.TestInfrastructure;
using KatLang.Tests.InvocationRoute;

namespace KatLang.Tests;

/// <summary>
/// Collection-builtin dispatch scaffolding (2026-11-17; an implementation-only optimization): the
/// call items of a collection builtin are one direct array fill (no LINQ iterator per call), its fixed
/// controls fill an array sized by the registry metadata (no growable list), and a prepared control is
/// read by kind through one checking helper (no closure or delegate per read). Values, errors with
/// their messages and spans, demand order, callback laziness, resource profiles and the agreement of
/// the three engines are unchanged; the outcomes pinned here are those of the commit before the change.
/// The strict allocation counts run in the isolated child process; the workload bounds are coarse.
/// </summary>
public class CollectionBuiltinDispatchTests
{
    // ── Programs: one outcome and one resource profile on the three engines ─────────────────────────

    // InvocationRouteCorpus.Core supplies IsBig, Square (which traces its argument), Inc and Add;
    // `trace` records each value it is applied to, in demand order.
    public static TheoryData<string, string, string, bool> Programs => new()
    {
        // Zero, one and two controls; value and callback controls; dot and plain spellings.
        { "count((1, 2, 3)), count([]), count(7)", "ok (3, 0, 1)", "", true },
        { "first([4, 5, 6]), last((4, 5, 6))", "ok (4, 6)", "", true },
        { "take([1, 2, 3], 2), [1, 2, 3].take(0), skip(range(1, 5), 3)", "ok ([1, 2], [], [4, 5])", "", true },
        { "contains((1, 2, 3), 2), [1, 2].contains(3), contains(('a', 'b'), 'b')", "ok (true, false, true)", "", true },
        { "[3, 1, 2].order, orderDesc((1, 3, 2)), distinct((1, 1, 2))", "ok ([1, 2, 3], [3, 2, 1], [1, 2])", "", true },
        { "sum((1, 2, 3)), min([4, 9, 2]), max([4, 9, 2]), avg((1, 2, 3, 4))", "ok (6, 2, 9, 2.5)", "", true },
        { "reduce([1, 2, 3], Add, 10), [1, 2, 3, 4].filter(IsBig).map(Inc)", "ok (16, [3, 4, 5])", "", true },
        { "take([1, 2, 3], count((1, 2))), skip([1, 2, 3], take([5], 1).count)", "ok ([1, 2], [2, 3])", "", true },
        // A callback is invoked per element, in order; an empty collection invokes none, and a VALUE
        // control is still demanded exactly once.
        { "[1, 2].map(Square), reduce([2], Add, trace(0))", "ok ([1, 4], 2)", "1,2,0", true },
        { "reduce([], Add, trace(7)), map([], Square), filter([], Square)", "ok (7, [], [])", "7", true },
        // The collection is demanded before the controls, the controls in written order.
        { "reduce(trace([1, 2]), Add, trace(0)), take(trace((1, 2, 3)), trace(2))", "ok (3, [1, 2])", "[1, 2],0,(1, 2, 3),2", true },
        // A failing control ends preparation: the later controls are neither demanded nor projected.
        { "reduce(trace([1]), 5, trace([1][5]))", "err BadIndex | while evaluating call to reduce: while evaluating call to trace: Bad index @[23:33, 23:34)", "[1]", true },
        { "take([1, 2], 1.5)", "err IllegalInEval | while evaluating call to take: Illegal in eval: take count must be exactly one whole-number value, but was 1.5 @[23:1, 23:18)", "", true },
        { "take([1, 2], (1, 2))", "err TypeMismatch | while evaluating call to take: Type mismatch: take count must be exactly one whole-number value, but was a sequence value with 2 sequence elements: (1, 2) @[23:1, 23:21)", "", true },
        { "reduce([1, 2], 5, 0)", "err NotAnAlgorithm | while evaluating call to reduce: The reduce reducer is not callable: the argument supplied for it is a value, not an algorithm. Pass an algorithm: a named algorithm, a builtin, or a block { ... }. @[23:16, 23:17)", "", true },
        { "map([1], 3)", "err NotAnAlgorithm | while evaluating call to map: The map transform is not callable: the argument supplied for it is a value, not an algorithm. Pass an algorithm: a named algorithm, a builtin, or a block { ... }. @[23:10, 23:11)", "", true },
        { "first([])", "err BadIndex | while evaluating call to first: first selects from an empty collection, which has no position to select: Bad index @[23:1, 23:10)", "", true },
        { "max([])", "err IllegalInEval | while evaluating call to max: Illegal in eval: max requires a non-empty collection @[23:1, 23:8)", "", true },
        // Cardinality is decided before any ordinary demand; an explicit spread is formed before it.
        { "take([trace(1)])", "err ArityMismatch | Callable `take(collection, count)` expects 2 arguments, but was called with 1 argument. @[23:1, 23:17)", "", true },
        { "count(), count(trace(1), trace(2))", "err ArityMismatch | Callable `count(collection)` expects 1 argument, but was called with 0 arguments. @[23:1, 23:8)", "", true },
        { "count([trace(1), trace(2)]*)", "err ArityMismatch | Callable `count(collection)` expects 1 argument, but was called with 2 arguments. @[23:1, 23:29)", "1,2", true },
        // A retained collector is observed selectively (NEED-07).
        { "C(*xs) = take(xs, 1)\nN(*xs) = count(xs)\nL(*xs) = last(xs)\nC(trace(1), trace(2)), N(trace(3), trace(4)), L(trace(5), trace(6))", "ok ([1], 2, 6)", "1,6", true },
        // The fused filter→count pipeline and its generic composition agree.
        { "range(1, 10).filter(IsBig).count, count(filter(range(1, 4), IsBig))", "ok (9, 3)", "", true },
        // An argument view is read by count/first/last and refused by every other collection builtin.
        { "First(meta op) = first(op.Arguments)\nInspect(Add(trace(1), 2)), First(Add(trace(5), 6))", "ok (2, 5)", "5", false },
        { "Total(meta op) = sum(op.Arguments)\nTotal(Add(trace(1), 2))", "err TypeMismatch | while evaluating call to Total: while evaluating call to sum: Type mismatch: An argument view supports only `count`, `first`, `last`, selection and an argument spread, not `sum`. @[23:18, 23:35)", "", false },
    };

    [Theory]
    [MemberData(nameof(Programs))]
    public async Task Program_HasThePinnedOutcome_AndOneResourceProfile_OnAllEngines(string source, string expected, string trace, bool plainToo)
    {
        foreach (var plain in plainToo ? new[] { true, false } : [false])
        {
            var c = new InvocationRouteCorpus.Case("CBD", source, Plain: plain);
            var generic = await InvocationRouteCorpus.Observe(c, 0);
            Assert.Equal(expected, generic.Outcome);
            Assert.Equal(trace, generic.Trace);
            var optimized = await InvocationRouteCorpus.Observe(c, 1);
            var asynchronous = await InvocationRouteCorpus.Observe(c, 2);
            Assert.Equal(generic.Semantic, optimized.Semantic);
            Assert.Equal(generic.Semantic, asynchronous.Semantic);
        }
    }

    // ── The call items: one per argument, in order, keeping its cell and written slot ────────────────

    private static readonly Type ItemType = typeof(Evaluator).GetNestedType("VariadicCallItem", BindingFlags.NonPublic)!;

    // The helper returns IReadOnlyList<VariadicCallItem> (a reference type), so it binds to an object-returning delegate.
    private static readonly Func<IReadOnlyList<Evaluator.ResolvedArgumentAlgorithm>, object> BuildItems =
        typeof(Evaluator).GetMethod("BuildCallableCallItems", BindingFlags.NonPublic | BindingFlags.Static)!
            .CreateDelegate<Func<IReadOnlyList<Evaluator.ResolvedArgumentAlgorithm>, object>>();

    private static Evaluator.ResolvedArgumentAlgorithm[] Arguments(int count)
        => Enumerable.Range(0, count)
            .Select(static i => new Evaluator.ResolvedArgumentAlgorithm(null)
            {
                Cell = NeedCell.Ready(new(new Result.Atom(i), 1)),
                Source = new Expr.Num(i),
            })
            .ToArray();

    private static object? Read(object item, string property) => ItemType.GetProperty(property)!.GetValue(item);

    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    [InlineData(2)]
    [InlineData(3)]
    public void CallItems_KeepEachArgumentsCellAndSource_InArgumentOrder(int count)
    {
        var args = Arguments(count);
        var items = ((IEnumerable)BuildItems(args)).Cast<object>().ToArray();
        Assert.Equal(count, items.Length);
        for (var i = 0; i < count; i++)
        {
            Assert.Same(args[i].Cell, Read(items[i], "Cell"));
            Assert.Same(args[i].Source, Read(items[i], "Source"));
            // Nothing is evaluated or projected while the items are built (CALL-03).
            Assert.Null(Read(items[i], "Value"));
            Assert.Null(Read(items[i], "ValueError"));
            Assert.Null(Read(items[i], "Algorithm"));
            Assert.Null(Read(items[i], "Callable"));
        }
    }

    // ── The defensive control readers keep their internal-metadata diagnostics ───────────────────────

    private static readonly Type PreparedType = typeof(Evaluator).GetNestedType("PreparedSequenceBuiltinSuffixArg", BindingFlags.NonPublic)!;

    private static object Prepared(string kind, object value)
        => Activator.CreateInstance(PreparedType.GetNestedType(kind)!, value)!;

    private static Array PreparedList(params object[] prepared)
    {
        var list = Array.CreateInstance(PreparedType, prepared.Length);
        for (var i = 0; i < prepared.Length; i++)
            list.SetValue(prepared[i], i);
        return list;
    }

    // A reader's verdict: "ok <value>" or its rendered error.
    private static string ReadControl(string reader, BuiltinId builtin, SequenceBuiltinSuffixArgDescriptor[] descriptors, Array prepared, int index)
    {
        var outcome = typeof(Evaluator).GetMethod(reader, BindingFlags.NonPublic | BindingFlags.Static)!
            .Invoke(null, [builtin, descriptors, prepared, index])!;
        var type = outcome.GetType();
        return (bool)type.GetProperty("IsError")!.GetValue(outcome)!
            ? "err " + KatLangError.FromEvalError((EvalError)type.GetProperty("Error")!.GetValue(outcome)!).Message
            : "ok " + type.GetProperty("Value")!.GetValue(outcome);
    }

    [Fact]
    public void ControlReaders_ReadTheirKind_AndReportEveryMetadataMismatch()
    {
        SequenceBuiltinSuffixArgDescriptor[] count = [new("count", SequenceBuiltinSuffixArgKind.WholeNumber)];
        SequenceBuiltinSuffixArgDescriptor[] item = [new("item", SequenceBuiltinSuffixArgKind.Value)];
        var whole = PreparedList(Prepared("WholeNumberArg", (Decimal128)2));
        var value = PreparedList(Prepared("ValueArg", new Result.Atom(5)));

        Assert.Equal("ok 2", ReadControl("ExpectPreparedWholeNumberSuffixArg", BuiltinId.take, count, whole, 0));
        Assert.Equal("ok Atom { Value = 5 }", ReadControl("ExpectPreparedValueSuffixArg", BuiltinId.contains, item, value, 0));
        Assert.Equal(
            "err internal sequence metadata for take prepared suffix argument 1 (count) did not match metadata kind whole-number value: Bad arity",
            ReadControl("ExpectPreparedWholeNumberSuffixArg", BuiltinId.take, count, value, 0));
        Assert.Equal(
            "err internal sequence metadata for contains expected suffix argument 1 (count) to have metadata kind value, but found whole-number value: Bad arity",
            ReadControl("ExpectPreparedValueSuffixArg", BuiltinId.contains, count, whole, 0));
        Assert.Equal(
            "err internal sequence metadata for take mismatched suffix arguments: Bad arity",
            ReadControl("ExpectPreparedWholeNumberSuffixArg", BuiltinId.take, count, PreparedList(), 0));
        Assert.Equal(
            "err internal sequence metadata for reduce expected suffix argument 2 to have metadata kind algorithm: Bad arity",
            ReadControl("ExpectPreparedAlgorithmSuffixArg", BuiltinId.reduce, count, whole, 1));
        Assert.Equal(
            "err internal sequence metadata for map prepared suffix argument 1 (count) did not match metadata kind algorithm: Bad arity",
            ReadControl("ExpectPreparedAlgorithmSuffixArg", BuiltinId.map, [new("count")], whole, 0));
    }

    // ── Program-level bounds (coarse, in-process) ───────────────────────────────────────────────────

    private const int Elements = 1_000;

    private static string Workload(string name) => name switch
    {
        // One zero-control call per element.
        "ZeroControl" => "F = count((x, x, x)) + x\nrange(1, 1000).map(F).sum",
        // Four calls per element, two of them reading one value control.
        "ValueControls" => "F = count(take((x, x, x), 2)) + count(skip((x, x), 1))\nrange(1, 1000).map(F).sum",
        // filter, map and reduce per element: four control reads, two callbacks invoked per item.
        "Callbacks" => "IsOdd = x mod 2 == 1\nInc = x + 1\nAdd(x, acc) = acc + x\nG = (x, x + 1).filter(IsOdd).map(Inc).reduce(Add, 0)\nrange(1, 1000).map(G).sum",
        _ => throw new ArgumentOutOfRangeException(nameof(name)),
    };

    /// <summary>
    /// Bytes per element of three collection-builtin workloads through <c>Evaluator.Run</c> with a fresh
    /// run cache: everything one run allocates, run-level tables included, divided by its 1,000 elements.
    /// Measured on 2026-11-17 on the Debug build (x64, .NET 11) before and after the change: ZeroControl
    /// 2,991.4 → 2,895.2, ValueControls 9,911.9 → 9,319.6, Callbacks 16,058.7 → 15,378.4 (88 bytes of LINQ
    /// iterator per call, 8 or 32 bytes of list per call, and 80 bytes of closure and delegate per control
    /// read). Each bound is the new value plus headroom and sits below the value before, so restoring the
    /// iterator, the list or the per-read delegate fails its row. Each window is the minimum of five runs,
    /// so one background-GC quantum moves a figure by at most about 8 bytes. The exact per-piece counts are
    /// the isolated child tests below.
    /// </summary>
    [Theory]
    [InlineData("ZeroControl", 2_940)]
    [InlineData("ValueControls", 9_600)]
    [InlineData("Callbacks", 15_700)]
    public void Workload_AllocationPerElement_StaysBelowTheMeasuredBound(string workload, int bound)
    {
        var program = new Expr.AlgorithmExpr(SourceProvenance.ParseValid(Workload(workload)).Root);
        Result Run()
        {
            var result = Evaluator.Run(program, new KatLang.Evaluation.Caching.RunScopedZeroArgPropertyResultCache(), enableLoopOptimization: true, loopDiagnostics: null);
            Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
            return result.Value;
        }

        for (var i = 0; i < 3; i++)
            _ = Run();
        var minimum = long.MaxValue;
        for (var i = 0; i < 5; i++)
        {
            var before = GC.GetAllocatedBytesForCurrentThread();
            _ = Run();
            minimum = Math.Min(minimum, GC.GetAllocatedBytesForCurrentThread() - before);
        }

        var perElement = minimum / (double)Elements;
        Assert.True(perElement < bound, $"{workload}: {perElement:F1} bytes per element (bound {bound})");
    }

    // ── Strict allocation counts (isolated child processes) ─────────────────────────────────────────

    private delegate EvalResult<Evaluator.CountedResult> ApplyResolved(
        BuiltinId builtin, IReadOnlyList<Evaluator.ResolvedArgumentAlgorithm> resolvedArgs, Evaluator.EvalCtx ctx,
        IReadOnlyList<(string Name, Result Value)> valEnv);

    private static readonly ApplyResolved Apply =
        typeof(Evaluator).GetMethod("ApplyBuiltinCountedResolved", BindingFlags.NonPublic | BindingFlags.Static)!
            .CreateDelegate<ApplyResolved>();

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

    private static Evaluator.ResolvedArgumentAlgorithm Supplied(Result value)
        => new(null) { Cell = NeedCell.Ready(new(value, value.ValueCount())) };

    private static readonly Type IterationItemsType = typeof(Evaluator).GetNestedType("CollectionIterationItems", BindingFlags.NonPublic)!;

    [Fact]
    public void CallItems_AllocateExactlyTheirItemArray_GcIsolatedChild()
    {
        if (!GcIsolatedAllocation.EnterChild())
            return;

        // Every successful collection-builtin call supplies at least its collection.
        foreach (var count in new[] { 1, 2, 3, 8 })
        {
            var args = Arguments(count);
            _ = BuildItems(args); // warm-up: first-call initialization stays outside the window
            var expected = ArrayBytes(ItemType, count);
            Assert.Equal(expected, Bytes(() => _ = BuildItems(args)));
        }
        GcIsolatedAllocation.Complete();
    }

    [Fact]
    public void ZeroControlDispatch_AllocatesOnlyItsItemsControlsAndView_GcIsolatedChild()
    {
        // first([5, 6, 7]) selects a stored element, so its dispatch allocates exactly the one-item call
        // items, the empty controls and the iteration view — no iterator and no list.
        if (!GcIsolatedAllocation.EnterChild())
            return;

        var ctx = Evaluator.EvalCtx.Empty;
        IReadOnlyList<(string Name, Result Value)> values = [];
        Evaluator.ResolvedArgumentAlgorithm[] args = [Supplied(new Result.ListValue([new Result.Atom(5), new Result.Atom(6), new Result.Atom(7)]))];
        var warm = Apply(BuiltinId.first, args, ctx, values);
        Assert.True(warm.IsOk, warm.IsError ? warm.Error.ToString() : null);
        Assert.Equal(5m, Assert.IsType<Result.Atom>(warm.Value.Value).Value);

        var expected = ArrayBytes(ItemType, 1) + ArrayBytes(PreparedType, 0) + ObjectBytes(IterationItemsType);
        Assert.Equal(expected, Bytes(() => _ = Apply(BuiltinId.first, args, ctx, values)));
        GcIsolatedAllocation.Complete();
    }

    [Fact]
    public void ControlReadingDispatch_AllocatesNoClosureOrDelegate_GcIsolatedChild()
    {
        // reduce([], Add, 0) prepares its callback and VALUE control and reads the initial accumulator,
        // which is its result: the dispatch allocates exactly the call items, the exact control array, the
        // two prepared controls and the iteration view.
        if (!GcIsolatedAllocation.EnterChild())
            return;

        var ctx = Evaluator.EvalCtx.Empty;
        IReadOnlyList<(string Name, Result Value)> values = [];
        Evaluator.ResolvedArgumentAlgorithm[] args =
        [
            Supplied(new Result.ListValue([])),
            new(new Algorithm.Builtin(BuiltinId.sum)),
            Supplied(new Result.Atom(0)),
        ];
        var warm = Apply(BuiltinId.reduce, args, ctx, values);
        Assert.True(warm.IsOk, warm.IsError ? warm.Error.ToString() : null);
        Assert.Equal(0m, Assert.IsType<Result.Atom>(warm.Value.Value).Value);

        var expected = ArrayBytes(ItemType, 3) + ArrayBytes(PreparedType, 2)
            + ObjectBytes(PreparedType.GetNestedType("AlgorithmArg")!) + ObjectBytes(PreparedType.GetNestedType("ValueArg")!)
            + ObjectBytes(IterationItemsType);
        Assert.Equal(expected, Bytes(() => _ = Apply(BuiltinId.reduce, args, ctx, values)));
        GcIsolatedAllocation.Complete();
    }
}
