using System.Globalization;
using System.Numerics;
using System.Reflection;
using KatLang.Evaluation;

namespace KatLang.Tests;

/// <summary>
/// <c>order</c> and <c>orderDesc</c> over dense whole numbers take a stable counting sort (November 2026,
/// implementation-only). Every other input keeps the comparison sort. Both must return the stable ascending
/// order of <see cref="Decimal128.CompareTo(Decimal128)"/>, or its exact reverse, as fresh atoms that keep
/// each input number's exact encoding (quantum and zero sign included), and reserve one materialized item
/// per result item. The selection rule is pinned at its boundaries. Both paths are compared with LINQ's
/// stable <c>OrderBy</c> on inputs full of equal-comparing values with different encodings.
/// </summary>
public class OrderBucketSortTests
{
    private delegate EvalResult<Evaluator.CountedResult> ApplyResolved(
        BuiltinId builtin, IReadOnlyList<Evaluator.ResolvedArgumentAlgorithm> resolvedArgs, Evaluator.EvalCtx ctx,
        IReadOnlyList<(string Name, Result Value)> valEnv);

    private static readonly ApplyResolved Apply =
        typeof(Evaluator).GetMethod("ApplyBuiltinCountedResolved", BindingFlags.NonPublic | BindingFlags.Static)!
            .CreateDelegate<ApplyResolved>();

    private static readonly Type NumbersType =
        typeof(Evaluator).GetNestedType("SingleAtomicNumberItems", BindingFlags.NonPublic)!;

    private static readonly MethodInfo BucketStarts =
        typeof(Evaluator).GetMethod("DenseWholeNumberBucketStarts", BindingFlags.NonPublic | BindingFlags.Static)!;

    private static Decimal128 D(string text) => Decimal128.Parse(text, CultureInfo.InvariantCulture);

    private static Result.Atom[] Atoms(IEnumerable<string> texts) => [.. texts.Select(static text => new Result.Atom(D(text)))];

    private static Result.Atom[] Atoms(IEnumerable<int> values) => [.. values.Select(static value => new Result.Atom(value))];

    // A permutation of 0..n-1 (7919 is prime and divides none of the sizes used here).
    private static IEnumerable<int> Permutation(int n) => Enumerable.Range(0, n).Select(i => (int)((i * 7919L) % n));

    public static TheoryData<string, string[], int, int[]?> Selections() => new()
    {
        { "permutation", ["3", "1", "2"], 1, [0, 1, 2] },
        { "repeats", ["5", "5", "7", "6", "5"], 5, [0, 3, 4] },
        { "span equals count", ["1", "4", "2", "3"], 1, [0, 1, 2, 3] },
        { "equal spellings and zeros", ["0", "-0", "1.0", "1E+0", "10E-1", "0E+3"], 0, [0, 3] },
        { "negatives", ["-2", "0", "-1", "-2"], -2, [0, 2, 3] },
        { "whole number with an exponent", ["1E+3", "999", "1001"], 999, [0, 1, 2] },
        { "top of int range", ["2147483647", "2147483646"], 2147483646, [0, 1] },
        { "bottom of int range", ["-2147483648", "-2147483647"], -2147483648, [0, 1] },
        { "span wider than int", ["-2147483648", "2147483647"], 0, null },
        { "span past count", ["1", "5", "2", "3"], 0, null },
        { "fraction", ["1", "2.5", "2"], 0, null },
        { "fraction first", ["0.5", "1"], 0, null },
        { "past int range", ["2147483647", "2147483648"], 0, null },
        { "below int range", ["-2147483649", "-2147483648"], 0, null },
        { "NaN", ["1", "NaN"], 0, null },
        { "infinity", ["1", "Infinity"], 0, null },
        { "negative infinity", ["-Infinity", "1"], 0, null },
        { "huge whole number", ["1", "1E+20"], 0, null },
        { "one item", ["7"], 0, null },
        { "no items", [], 0, null },
    };

    /// <summary>
    /// Whole numbers in <see cref="int"/> range spanning at most as many integers as there are items get
    /// bucket starts; anything else (a fraction, a value past int range, NaN, an infinity, a wider span,
    /// fewer than two items) gets none, and the comparison sort runs.
    /// </summary>
    [Theory]
    [MemberData(nameof(Selections))]
    public void DenseWholeNumberSelection_HoldsAtItsBoundaries(string name, string[] values, int lowest, int[]? starts)
    {
        var numbers = Activator.CreateInstance(NumbersType, new object[] { Atoms(values) });
        object?[] arguments = [numbers, 0];
        var actual = (int[]?)BucketStarts.Invoke(null, arguments);
        Assert.True(starts is null == actual is null, $"{name}: expected {(starts is null ? "the comparison sort" : "buckets")}.");
        if (starts is null)
            return;
        Assert.Equal(starts, actual);
        Assert.Equal(lowest, (int)arguments[1]!);
    }

    private static IEnumerable<(string Name, Result.Atom[] Items)> Inputs()
    {
        yield return ("dense permutation", Atoms(Permutation(2_000).Select(static v => v + 1)));
        yield return ("dense negative repeats", Atoms(Permutation(2_000).Select(static v => (v % 300) - 150)));
        string[] spellings = ["1", "1.0", "1.00", "10E-1", "0", "-0", "0.0", "0E+2", "2", "2E+0", "-1", "-1.000"];
        yield return ("dense spellings", Atoms(Permutation(600).Select(v => spellings[v % spellings.Length])));
        yield return ("span equals count", Atoms(Permutation(1_000).Select(static v => v - 500)));
        yield return ("span one past count", Atoms(Permutation(1_000).Select(static v => v == 999 ? 1_000 : v)));
        yield return ("sparse", Atoms(Permutation(1_000).Select(static v => 3 * v)));
        yield return ("fractions", Atoms(Permutation(1_000).Select(static v => (v % 50) + (v % 2 == 0 ? ".50" : ".5"))));
        yield return ("specials among dense", Atoms(Permutation(500).Select(static v => v switch
        {
            7 => "NaN",
            11 => "Infinity",
            13 => "-Infinity",
            17 => "-0",
            _ => (v % 40).ToString(CultureInfo.InvariantCulture),
        })));
        yield return ("outlier last", Atoms(Permutation(1_000).Select(static v => (v + 1).ToString(CultureInfo.InvariantCulture)).Append("1E+20")));
        yield return ("descending run", Atoms(Enumerable.Range(0, 1_000).Select(static i => 1_000 - i)));
        yield return ("ascending run", Atoms(Enumerable.Range(0, 1_000)));

        var random = new Random(20261121);
        string[] pool =
        [
            "1", "1.0", "1.00", "0", "-0", "0.0", "-3", "-3.000", "7", "7E+0", "70E-1", "2.5", "2.50",
            "2147483647", "-2147483648", "2147483648", "NaN", "Infinity", "-Infinity", "1E+40",
        ];
        foreach (var n in new[] { 2, 3, 17, 100, 1_000, 5_000 })
        {
            for (var kind = 0; kind < 5; kind++)
            {
                var values = Enumerable.Range(0, n).Select(i => kind switch
                {
                    0 => pool[random.Next(pool.Length)],
                    1 => random.Next(-5, 6).ToString(CultureInfo.InvariantCulture),
                    2 => random.Next(-5, 6) + (random.Next(3) == 0 ? ".0" : ""),
                    3 => (i / 3).ToString(CultureInfo.InvariantCulture),
                    _ => ((n - i) / 2).ToString(CultureInfo.InvariantCulture),
                }).ToArray();
                yield return ($"random kind {kind}, {n} items", Atoms(values));
            }
        }
    }

    [Fact]
    public void OrderAndOrderDesc_ReturnTheStableComparisonOrder_AsFreshAtoms_OnBothSorts()
    {
        int bucketed = 0, compared = 0;
        foreach (var (name, items) in Inputs())
        {
            var numbers = Activator.CreateInstance(NumbersType, new object[] { items });
            if (BucketStarts.Invoke(null, [numbers, 0]) is null)
                compared++;
            else
                bucketed++;

            var stable = items.Select(static atom => atom.Value).OrderBy(static value => value, Comparer<Decimal128>.Default)
                .Select(Decimal128.EncodeBinary).ToArray();
            var inputs = new HashSet<Result>(items, ReferenceEqualityComparer.Instance);
            foreach (var (builtin, descending) in new[] { (BuiltinId.order, false), (BuiltinId.orderDesc, true) })
            {
                var ctx = Evaluator.EvalCtx.Empty;
                var collection = new Result.ListValue(items);
                var result = Apply(builtin, [new(null) { Cell = NeedCell.Ready(new(collection, 1)) }], ctx, []);
                Assert.True(result.IsOk, $"{name}, {builtin}: {(result.IsError ? result.Error.ToString() : null)}");
                var sorted = Assert.IsType<Result.ListValue>(result.Value.Value).Items;

                var expected = descending ? Enumerable.Reverse(stable).ToArray() : stable;
                var actual = sorted.Select(static item => Decimal128.EncodeBinary(Assert.IsType<Result.Atom>(item).Value)).ToArray();
                Assert.True(expected.SequenceEqual(actual), $"{name}, {builtin}: not the stable order of the input encodings.");
                Assert.True(sorted.All(item => !inputs.Contains(item)), $"{name}, {builtin}: an input atom was returned instead of a fresh one.");
                Assert.Equal(items.Length, ctx.Budget.MaterializedItems);
            }
        }

        // Both sorts were exercised many times.
        Assert.True(bucketed >= 10 && compared >= 10, $"{bucketed} inputs bucketed, {compared} compared.");
    }
}
