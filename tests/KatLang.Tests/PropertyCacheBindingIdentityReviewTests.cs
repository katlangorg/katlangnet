using System.Numerics;
using KatLang.Evaluation.Caching;
using KatLang.Tests.AsyncEvaluation;

namespace KatLang.Tests;

public class PropertyCacheBindingIdentityReviewTests
{
    public static TheoryData<string, int, int[]> Cases() => new()
    {
        { "Outer(x) = { A = Tick() + x\n F(y) = A\n G(y) = F(y)\n A, F(0), G(0), A, Outer.A }\nOuter(0)\nOuter(0)",
            2, [1, 1, 1, 1, 1, 2, 2, 2, 2, 2] },
        { "Outer(x) = { A = Tick() + x\n A, map([1, 2], {y * 0 + A}), A }\nOuter(0)\nOuter(0)",
            2, [1, 1, 1, 1, 2, 2, 2, 2] },
        { "Outer(x) = { A = Tick() + x\n A, [1, 2].filter({y < A + 2}).count, A }\nOuter(0)\nOuter(0)",
            2, [1, 2, 1, 2, 2, 2] },
        { "Outer(x) = { A = Tick() + x\n F(y) = if(A > 0, y, 0)\n R(e, a) = a + A\n A, filter([1, 2], {y < A + 2}), reduce([1, 2], R, A), A }\nOuter(0)",
            1, [1, 1, 2, 3, 1] },
        { "Outer(x) = { Lib = { public A = Tick() + x\n A }\n Read = { open Lib\n A }\n Lib.A, Read, Lib, Lib.A, Lib.A.string.count }\nOuter(0)\nOuter(0)",
            2, [1, 1, 1, 1, 1, 2, 2, 2, 2, 1] },
        { "Outer(x) = { Inner = { A = Tick() + x\n F(y) = A\n A, F(0), A }\n Inner(), Inner() }\nOuter(0)",
            2, [1, 1, 1, 2, 2, 2] },
        { "Outer(x) = { A = Tick() + x\n Step(s) = s + A\n A, repeat(Step, 2, 0), A }\nOuter(0)\nOuter(0)",
            2, [1, 2, 1, 2, 4, 2] },
        { "A = Tick()\n Outer(x) = { A = Tick() + x\n F(y) = A\n A, F(0), A }\n A, Outer(0), A, Outer(0), A",
            3, [1, 2, 2, 2, 1, 3, 3, 3, 1] },
        { "Outer(x) = { A = Tick() + x\n A, A(), A, Outer.A(), Outer.A }\nOuter(0)\nOuter(0)",
            6, [1, 2, 1, 3, 1, 4, 5, 4, 6, 4] },
        { "Outer(x) = { open Lib\n Lib = { public A = Tick() + x }\n A(), Lib.A, A, Lib.A(), A }\nOuter(0)\nOuter(0)",
            6, [1, 2, 2, 3, 2, 4, 5, 5, 6, 5] },
    };

    [Theory]
    [MemberData(nameof(Cases))]
    public async Task BindingIdentity_SurvivesConsumersAndExplicitCalls(string source, int expectedCalls, int[] expected)
    {
        // An increasing host result makes both duplicate evaluation and cache poisoning
        // observable without relying on a random sequence or the cache's implementation.
        foreach (var path in new[] { 0, 1, 2 })
        {
            var calls = 0;
            var operations = HostOperations.Create(HostOperation.Create("Tick", (_, _) => new Result.Atom(++calls)));
            var ast = new Expr.AlgorithmExpr((await SourceProvenance.ParseValidAsync(source, new RunOptions { HostOperations = operations })).Root);
            EvalResult<Evaluator.CountedResult> result;
            if (path == 2)
            {
                var cache = new HoldingAsyncZeroArgPropertyResultCache(1);
                var pending = Evaluator.RunCountedObservedAsync(ast, zeroArgPropertyResultCache: cache, hostOperations: operations);
                await cache.Reached.WaitAsync(TimeSpan.FromSeconds(10));
                Assert.False(pending.IsCompleted);
                cache.Release();
                (result, _) = await AsyncEvaluationHarness.Complete(pending);
                Assert.True(cache.AsyncAccesses > 1);
            }
            else
            {
                (result, _) = Evaluator.RunCountedObserved(ast, enableOptimizations: path == 1, hostOperations: operations);
            }
            Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
            Assert.Equal(expected.Select(static x => (Decimal128)x), Flatten(result.Value.Value));
            Assert.Equal(expectedCalls, calls);
        }
    }

    private static IEnumerable<Decimal128> Flatten(Result value) => value switch
    {
        Result.Atom atom => [atom.Value],
        Result.SequenceValue sequence => sequence.Items.SelectMany(Flatten),
        Result.ListValue list => list.Items.SelectMany(Flatten),
        _ => throw new Xunit.Sdk.XunitException($"Unexpected value {value}"),
    };

    [Fact]
    public void DistinctOwnerDeclarations_SharingTheSamePropertyList_DoNotAlias()
    {
        var binding = new Property("A", new Algorithm.User(null, [], [], [], [new Expr.Num(1)]));
        Property[] properties = [binding];
        var first = new Algorithm.User(null, [], [], properties, []);
        var second = new Algorithm.User(null, [], [], properties, []);
        var baseline = new ZeroArgPropertyExecution(first, binding, ZeroArgPropertyAccessKind.Lexical,
            new object(), new object(), new object(), new object());
        var comparer = ZeroArgPropertyCacheKeyComparer.Instance;
        Assert.False(comparer.Equals(ZeroArgPropertyCacheKey.FromExecution(baseline),
            ZeroArgPropertyCacheKey.FromExecution(baseline with { Owner = second })));
        Assert.True(comparer.Equals(ZeroArgPropertyCacheKey.FromExecution(baseline),
            ZeroArgPropertyCacheKey.FromExecution(baseline with { Owner = first with { } })));
    }

    [Fact]
    public async Task HostDag_SharedMemberInDistinctOwners_HasDistinctValues()
    {
        var calls = 0;
        var operations = HostOperations.Create(HostOperation.Create("Tick", (_, _) => new Result.Atom(++calls)));
        var parsed = await SourceProvenance.ParseValidAsync("A = Tick()\nA", new RunOptions { HostOperations = operations });
        var first = new Algorithm.User(null, [], [], parsed.Root.Properties, []);
        var second = new Algorithm.User(null, [], [], parsed.Root.Properties, []);
        Expr Read(Algorithm owner) => new Expr.DotCall(new Expr.AlgorithmExpr(owner), "A", null);
        var ast = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [], [],
            [Read(first), Read(second), Read(first with { }), Read(second with { })]));
        var (result, _) = Evaluator.RunCountedObserved(ast, hostOperations: operations);
        Assert.False(result.IsError, result.IsError ? result.Error.ToString() : null);
        Assert.Equal([1m, 2m, 1m, 2m], result.Value.Value.ToAtoms());
        Assert.Equal(2, calls);
    }
}
