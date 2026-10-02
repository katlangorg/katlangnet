using System.Collections;
using System.Numerics;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;

namespace KatLang.Tests;

public class PropertyBindingIndexTests
{
    private static Algorithm.User Body(IReadOnlyList<Property> properties, params Expr[] output)
        => new(null, [], [], properties, new OutputBundle(output));

    private static Property Constant(string name, int value, bool isPublic = false,
        PropertyExposure exposure = PropertyExposure.Exported)
        => new(name, Body([], new Expr.Num(value)), isPublic, exposure);

    // The independent oracle is the original ordered scan, including exact binding identity.
    private static Property? Linear(IReadOnlyList<Property> properties, string name)
    {
        foreach (var property in properties)
            if (property.Name == name)
                return property;
        return null;
    }

    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    [InlineData(31)]
    [InlineData(32)]
    [InlineData(33)]
    [InlineData(128)]
    [InlineData(1024)]
    public void Selection_IsReferenceIdenticalToLinearLookup(int width)
    {
        var random = new Random(1907 + width);
        string[] names = ["A", "a", "", "İ", "I", "é", "e\u0301", "Aa", "BB", "count"];
        var properties = Enumerable.Range(0, width).Select(i => Constant(
            names[random.Next(names.Length)], i, i % 2 == 0,
            i % 3 == 0 ? PropertyExposure.LocalOnlyCapturedAncestorParameters : PropertyExposure.Exported)).ToArray();
        var lookup = new PropertyBindingIndexCache();
        // A miss can build the index too; repeated hits and misses keep the first binding.
        foreach (var name in new[] { "missing" }.Concat(names).Concat(names.Reverse()).Append("MISSING"))
            Assert.Same(Linear(properties, name), lookup.Lookup(properties, name));
    }

    [Fact]
    public void LargeList_IsReadOnce_ForHitsAndMissesAcrossWiredViews()
    {
        var properties = new ObservedProperties(Enumerable.Range(0, 512)
            .Select(i => Constant($"P{i}", i)).ToArray());
        var owner = Body(properties);
        var view = owner with { Parent = new ScopeCtx(null, [], []) };
        var budget = EvaluationBudget.Create(null);
        Assert.Null(budget.PropertyBindings.Lookup(owner.Properties, "missing"));
        Assert.Equal(512, properties.Reads);
        for (var i = 0; i < 512; i++)
        {
            Assert.Same(properties.Items[i], budget.PropertyBindings.Lookup(view.Properties, $"P{i}"));
            Assert.Null(budget.PropertyBindings.Lookup(view.Properties, $"missing{i}"));
        }
        Assert.Equal(512, properties.Reads);
        Assert.Same(budget.PropertyBindings, budget.PropertyBindings);
        Assert.NotSame(budget.PropertyBindings, EvaluationBudget.Create(null).PropertyBindings);
    }

    [Fact]
    public void SmallList_KeepsEarlyExitAndAllocatesNoIndex()
    {
        var properties = new ObservedProperties([Constant("First", 1), Constant("Last", 2)]);
        var lookup = new PropertyBindingIndexCache();
        Assert.Same(properties.Items[0], lookup.Lookup(properties, "First"));
        Assert.Equal(1, properties.Reads);
        // Changing a small list within this helper test proves that it was not indexed.
        // Evaluator callers still keep executable metadata stable throughout each run.
        properties.Items[0] = Constant("Changed", 3);
        Assert.Same(properties.Items[0], lookup.Lookup(properties, "Changed"));
        Assert.Equal(2, properties.Reads);
    }

    [Fact]
    public void ListKeys_UseReferenceIdentity_AndWithCopiesCanReplaceProperties()
    {
        var first = new ObservedProperties(Enumerable.Range(0, 64).Select(i => Constant($"P{i}", i)).ToArray());
        var second = new ObservedProperties(first.Items.Select(p => p with { }).ToArray());
        Assert.True(first.Equals(second)); // Deliberately equal list objects, distinct bindings.
        var owner = Body(first);
        var copy = owner with { Properties = second };
        Assert.Same(owner.Declaration, copy.Declaration);
        var lookup = new PropertyBindingIndexCache();
        Assert.Same(first.Items[63], lookup.Lookup(owner.Properties, "P63"));
        Assert.Same(second.Items[63], lookup.Lookup(copy.Properties, "P63"));
        Assert.Equal(64, first.Reads);
        Assert.Equal(64, second.Reads);
    }

    [Fact]
    public void DuplicateNames_SelectTheFirstInstance_RegardlessOfVisibilityOrExposure()
    {
        var first = Constant("X", 1, exposure: PropertyExposure.LocalOnlyCapturedAncestorParameters);
        var equalCopy = first with { };
        Assert.Equal(first, equalCopy);
        Property[] properties = [first, equalCopy, Constant("X", 2, isPublic: true),
            .. Enumerable.Range(0, 64).Select(i => Constant($"Pad{i}", i))];
        Assert.Same(first, new PropertyBindingIndexCache().Lookup(properties, "X"));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task EvaluatorLocalAndParentLookups_UseTheRunsIndex(bool nested)
    {
        foreach (var route in new[] { 0, 1, 2 })
        {
            var properties = new ObservedProperties(Enumerable.Range(0, 64)
                .Select(i => Constant($"P{i}", i)).ToArray());
            Expr output = new Expr.Resolve("P63");
            if (nested)
                output = new Expr.AlgorithmExpr(Body([], output));
            var expr = new Expr.AlgorithmExpr(Body(properties, output));
            var (result, budget) = route == 2
                ? await Evaluator.RunCountedObservedAsync(expr,
                    zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache())
                : Evaluator.RunCountedObserved(expr, enableOptimizations: route == 1);
            Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : "");
            Assert.Equal((Decimal128)63, result.Value.Value.AsNum());
            var readsAfterEvaluation = properties.Reads;
            Assert.Same(properties.Items[63], budget.PropertyBindings.Lookup(properties, "P63"));
            Assert.Null(budget.PropertyBindings.Lookup(properties, "missing"));
            Assert.Equal(readsAfterEvaluation, properties.Reads);
        }
    }

    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    [InlineData(2)]
    public async Task SharedIndexedPropertyList_KeepsDistinctOwnersValueCacheEntries(int route)
    {
        var ticks = 0;
        Result Tick() => new Result.Atom((Decimal128)(++ticks));
        var operations = HostOperations.Create(route == 2
            ? HostOperation.CreateAsync("tick", async (_, _) => { await Task.Yield(); return Tick(); })
            : HostOperation.Create("tick", (_, _) => Tick()));
        Property[] shared = [.. Enumerable.Range(0, 64).Select(i => Constant($"Pad{i}", i)),
            new("Read", Body([], new Expr.NativeCall("host:tick", [])))];
        var left = Body(shared, new Expr.Resolve("Read"), new Expr.Resolve("Read"));
        var right = Body(shared, new Expr.Resolve("Read"), new Expr.Resolve("Read"));
        Assert.NotSame(left.Declaration, right.Declaration);
        var expr = new Expr.AlgorithmExpr(Body([new("Left", left), new("Right", right)],
            new Expr.Resolve("Left"), new Expr.Resolve("Right")));
        var (result, _) = route == 2
            ? await Evaluator.RunCountedObservedAsync(expr, hostOperations: operations)
            : Evaluator.RunCountedObserved(expr, enableOptimizations: route == 1, hostOperations: operations);
        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : "");
        Assert.Equal(new Decimal128[] { 1, 1, 2, 2 }, result.Value.Value.ToHostAtoms());
        Assert.Equal(2, ticks);
    }

    [Fact]
    public async Task HostListEdits_BetweenRuns_AreObservedIncludingSameCountEdits()
    {
        var properties = Enumerable.Range(0, 64).Select(i => Constant($"Pad{i}", i)).ToList();
        properties.Add(Constant("X", 1));
        properties.Add(Constant("Y", 2));
        var root = Body(properties, new Expr.Resolve("X"));
        async Task AssertEveryEvaluator(int expected)
        {
            var expr = new Expr.AlgorithmExpr(root);
            var direct = Evaluator.Run(expr);
            Assert.True(direct.IsOk, direct.IsError ? direct.Error.ToString() : "");
            Assert.Equal((Decimal128)expected, direct.Value.AsNum());
            var asyncDirect = await Evaluator.RunAsync(expr);
            Assert.True(asyncDirect.IsOk, asyncDirect.IsError ? asyncDirect.Error.ToString() : "");
            Assert.Equal((Decimal128)expected, asyncDirect.Value.AsNum());
            foreach (var optimized in new[] { false, true })
            {
                var (result, _) = Evaluator.RunCountedObserved(expr, enableOptimizations: optimized);
                Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : "");
                Assert.Equal((Decimal128)expected, result.Value.Value.AsNum());
                Assert.Equal(1, result.Value.EmittedCount);
            }
            var (twin, _) = await Evaluator.RunCountedObservedAsync(expr,
                zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache());
            Assert.True(twin.IsOk, twin.IsError ? twin.Error.ToString() : "");
            Assert.Equal((Decimal128)expected, twin.Value.Value.AsNum());
        }
        await AssertEveryEvaluator(1);
        properties[64] = Constant("X", 3); // Same count, new binding.
        await AssertEveryEvaluator(3);
        (properties[64], properties[65]) = (properties[65], properties[64]);
        await AssertEveryEvaluator(3);
        properties[64] = Constant("X", 2);
        properties[65] = Constant("Y", 3); // Same count, rename both bindings.
        await AssertEveryEvaluator(2);
        properties.RemoveAt(65);
        await AssertEveryEvaluator(2);
        properties.Insert(0, Constant("Z", 4));
        await AssertEveryEvaluator(2);
        properties[65] = Constant("Y", 2);
        properties[0] = Constant("X", 4);
        await AssertEveryEvaluator(4);
        root = root with { Properties = [Constant("X", 5), .. properties.Where(p => p.Name != "X")] };
        await AssertEveryEvaluator(5);
    }

    private static string Padding => string.Concat(Enumerable.Range(0, 64).Select(i => $"Pad{i} = {i}\n"));

    [Theory]
    [InlineData("X = 10\nLib = { public X = 20 }\nOuter = {\nopen Lib\n{PAD}Inner = X\nInner\n}\nOuter", "ok 10")]
    [InlineData("X = 10\nOuter = {\n{PAD}X = 20\nInner = X\nInner\n}\nOuter", "ok 20")]
    [InlineData("Lib = {\n{PAD}public Only(*xs) = tick()\n}\nA = Lib.Only\nB = A\nB, Lib.Only, A, B", "ok S[1, 2, 3, 1] [tick#1,tick#2,tick#3]")]
    [InlineData("Outer(x) = {\n{PAD}Value = tick() + x\nInner = { Value, Value }\nInner\n}\nOuter(10), Outer(20)", "ok S[S[11, 11], S[22, 22]] [tick#1,tick#2]")]
    [InlineData("Lib = {\n{PAD}public X = tick()\n}\nRead = {\nopen Lib\n{PAD}X, Lib.X, X\n}\nRead", "ok S[1, 1, 1] [tick#1]")]
    [InlineData("Inc(x) = x + 1\nA = Inc\nB = A\nOuter = {\n{PAD}Inc(x) = x + 100\nB(1)\n}\nOuter", "ok 2")]
    [InlineData("Step(x) = {\n{PAD}Next = x + 1\nNext\n}\nrepeat(Step, 20, 0)", "ok 20")]
    public async Task IndexedScopes_PreserveOwnershipCacheAndAliasesOnSixRoutes(string source, string expected)
    {
        source = Padding + source.Replace("{PAD}", Padding, StringComparison.Ordinal);
        Assert.Equal(expected, RepeatedNameConstraintTests.Rendered(
            await RepeatedNameConstraintTests.OnEveryRouteAsync(source)));
    }

    private sealed class ObservedProperties(Property[] items) : IReadOnlyList<Property>
    {
        internal Property[] Items { get; } = items;
        internal int Reads { get; private set; }
        public int Count => Items.Length;
        public Property this[int index] { get { Reads++; return Items[index]; } }
        public IEnumerator<Property> GetEnumerator()
        {
            for (var i = 0; i < Count; i++)
                yield return this[i];
        }
        IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();
        public override bool Equals(object? obj) => obj is ObservedProperties;
        public override int GetHashCode() => 0;
    }
}
