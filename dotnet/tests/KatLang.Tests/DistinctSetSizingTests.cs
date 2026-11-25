using System.Numerics;
using System.Reflection;
using KatLang.Evaluation;

namespace KatLang.Tests;

/// <summary>
/// Compare the production first-occurrence pass with the original HashSet, recording every
/// hash and ordered equality call under forced collisions, the kept positions and the work charged.
/// </summary>
public class DistinctSetSizingTests
{
    private sealed class Recording(Result.ValueSemanticComparer inner, Dictionary<Result, int> positions, int fold) : IEqualityComparer<Result>
    {
        internal readonly List<string> Log = [];

        public bool Equals(Result? x, Result? y)
        {
            var equal = inner.Equals(x, y);
            Log.Add($"E{positions[x!]},{positions[y!]}={(equal ? 1 : 0)}");
            return equal;
        }

        public int GetHashCode(Result obj)
        {
            var hash = inner.GetHashCode(obj);
            if (fold > 0)
                hash = (int)((uint)hash % (uint)fold);
            Log.Add($"H{positions[obj]}={hash}");
            return hash;
        }
    }

    private static Result Atom(decimal value) => new Result.Atom((Decimal128)value);

    private static Result Pair(int value) => new Result.ListValue([Atom(value), new Result.ListValue([Atom(value)])]);

    public static TheoryData<string> Inputs() => new() { "mod1", "mod7", "mod97", "distinct", "pairs", "mixed", "pages" };

    private static Result[] Items(string name) => name switch
    {
        "mod1" => [.. Enumerable.Range(0, 600).Select(static i => Atom(0))],
        "mod7" => [.. Enumerable.Range(0, 600).Select(static i => Atom(i % 7))],
        "mod97" => [.. Enumerable.Range(0, 600).Select(static i => Atom(i % 97))],
        "distinct" => [.. Enumerable.Range(0, 600).Select(static i => Atom(i))],
        // Fresh structured values: every hash and every duplicate's equality walks and charges structure.
        "pages" => [.. Enumerable.Range(0, 4_500).Select(static i => Atom(i % 2_117))],
        "pairs" => [.. Enumerable.Range(0, 600).Select(static i => Pair(i % 150))],
        _ => Mixed(),
    };

    private static Result[] Mixed()
    {
        var shared = new Result.ListValue([Atom(1), Atom(2)]);
        return
        [
            Atom(1), Atom(1.0m), Atom(1.00m), Atom(0), new Result.Atom(-(Decimal128)0), shared, shared,
            new Result.ListValue([Atom(1), Atom(2)]), new Result.ListValue([Atom(1.0m), Atom(2)]),
            new Result.ListValue([shared, shared]), new Result.ListValue([new Result.ListValue([Atom(1), Atom(2)]), shared]),
            new Result.SequenceValue([Atom(1), Atom(2)]), new Result.Str("a"), new Result.Str("a"), new Result.Str("b"),
            new Result.ListValue([]), new Result.SequenceValue([]), Atom(2),
        ];
    }

    private delegate int MarkPositions(IEqualityComparer<Result> comparer, IReadOnlyList<Result> items, ulong[] positions);

    private static readonly MarkPositions MarkPaged =
        typeof(Evaluator).GetMethod("MarkDistinctPositions", BindingFlags.NonPublic | BindingFlags.Static)!
            .CreateDelegate<MarkPositions>();

    private static (int Count, ulong[] Bits, long Work, long Steps, List<string> Calls) Fill(
        Result[] items, int fold, bool paged)
    {
        var positions = new Dictionary<Result, int>(ReferenceEqualityComparer.Instance);
        for (var i = 0; i < items.Length; i++)
            positions.TryAdd(items[i], i);
        var budget = EvaluationBudget.Create(null);
        var inner = Result.CreateOperationComparer(budget);
        var comparer = new Recording(inner, positions, fold);
        var bits = new ulong[(items.Length + 63) / 64];
        int count;
        if (paged)
            count = MarkPaged(comparer, items, bits);
        else
        {
            var seen = new HashSet<Result>(comparer);
            for (var i = 0; i < items.Length; i++)
            {
                if (seen.Add(items[i]))
                    bits[i / 64] |= 1UL << (i % 64);
            }
            count = seen.Count;
        }

        Assert.Null(inner.CompleteOperation());
        return (count, bits, budget.ConsumedStructuralWorkUnits, budget.ConsumedSteps, comparer.Log);
    }

    [Theory]
    [MemberData(nameof(Inputs))]
    public void PagedSet_PreservesTheHashSetsComparerCallsAndCharges(string input)
    {
        var items = Items(input);
        // Force collisions across page expansions without logging a quadratic one-bucket trace.
        int[] folds = input == "pages" ? [0, 64] : [0, 1, 3, 64];
        foreach (var fold in folds)
        {
            var expected = Fill(items, fold, paged: false);
            var actual = Fill(items, fold, paged: true);
            Assert.Equal(expected.Count, actual.Count);
            Assert.Equal(expected.Bits, actual.Bits);
            Assert.Equal(expected.Work, actual.Work);
            Assert.Equal(expected.Steps, actual.Steps);
            Assert.Equal(expected.Calls, actual.Calls);
        }
    }

    private delegate EvalResult<Evaluator.CountedResult> ApplyResolved(
        BuiltinId builtin, IReadOnlyList<Evaluator.ResolvedArgumentAlgorithm> resolvedArgs, Evaluator.EvalCtx ctx,
        IReadOnlyList<(string Name, Result Value)> valEnv);

    private static readonly ApplyResolved Apply =
        typeof(Evaluator).GetMethod("ApplyBuiltinCountedResolved", BindingFlags.NonPublic | BindingFlags.Static)!
            .CreateDelegate<ApplyResolved>();

    /// <summary>
    /// 9,000 fresh structured items with 6,000 distinct values exercise several page expansions. The kept items (by reference, in order) and the structural
    /// work and steps charged equal those of the same comparer filling a set that only doubles.
    /// </summary>
    [Fact]
    public void Distinct_PastTheSizingPoint_KeepsTheGrownSetsFirstOccurrencesAndWork()
    {
        var items = Enumerable.Range(0, 9_000).Select(static i => Pair((int)((i * 7919L) % 6_000))).ToArray();
        var collection = new Result.ListValue(items);
        var stored = ((Result.ListValue)collection).Items;

        var referenceBudget = EvaluationBudget.Create(null);
        var comparer = Result.CreateOperationComparer(referenceBudget);
        var seen = new HashSet<Result>(comparer);
        var expected = stored.Where(seen.Add).ToList();
        Assert.Null(comparer.CompleteOperation());
        Assert.Equal(6_000, expected.Count);
        Assert.True(referenceBudget.ConsumedStructuralWorkUnits > 0);

        var ctx = Evaluator.EvalCtx.Empty;
        var result = Apply(BuiltinId.distinct, [new(null) { Cell = NeedCell.Ready(new(collection, 1)) }], ctx, []);
        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : null);
        var kept = Assert.IsType<Result.ListValue>(result.Value.Value).Items;
        Assert.Equal(expected.Count, kept.Count);
        for (var i = 0; i < kept.Count; i++)
            Assert.Same(expected[i], kept[i]);
        Assert.Equal(referenceBudget.ConsumedStructuralWorkUnits, ctx.Budget.ConsumedStructuralWorkUnits);
        Assert.Equal(referenceBudget.ConsumedSteps, ctx.Budget.ConsumedSteps);
    }
}
