using System.Reflection;
using KatLang.Evaluation;
using KatLang.Tests.InvocationRoute;

namespace KatLang.Tests;

/// <summary>
/// PERF-ORD-1: the ordinary-call binding lookups (<c>LookupNeed</c>, <c>LookupVal</c>, the small-list
/// property scan) and the multi-name binder's environment scan without an interface enumerator. These
/// are implementation-only optimizations. The oracle for each helper is the original ordered
/// first-match scan, and the allocation guards hold at every JIT tier, because indexed access boxes
/// nothing. The source programs pin ordinary named, member, extension, conditional-family and META
/// behavior with resource parity on the three engines.
/// </summary>
public class OrdinaryCallLookupTests
{
    private delegate NeedCell? NeedLookup(IReadOnlyList<(string Name, NeedCell Cell)> env, string name);
    private delegate Result? ValueLookup(IReadOnlyList<(string Name, Result Value)> env, string name);

    private static readonly NeedLookup LookupNeed = typeof(Evaluator)
        .GetMethod("LookupNeed", BindingFlags.NonPublic | BindingFlags.Static)!.CreateDelegate<NeedLookup>();

    private static readonly ValueLookup LookupVal = typeof(Evaluator)
        .GetMethod("LookupVal", BindingFlags.NonPublic | BindingFlags.Static)!.CreateDelegate<ValueLookup>();

    private static T? Linear<T>(IReadOnlyList<(string Name, T Item)> env, string name) where T : class
    {
        foreach (var (n, item) in env)
            if (n == name) return item;
        return null;
    }

    private static NeedCell Cell(int value) => NeedCell.Ready(new(new Result.Atom(value), 1));

    // Every concrete environment shape the evaluator builds: Concat's List, binder arrays, collection
    // expressions (a single binding and the empty environment).
    private static IEnumerable<IReadOnlyList<(string Name, T Item)>> Shapes<T>((string, T)[] bindings)
    {
        yield return bindings;
        yield return bindings.ToList();
        yield return bindings.ToList().AsReadOnly();
        if (bindings.Length == 1) yield return [bindings[0]];
        if (bindings.Length == 0) yield return [];
    }

    private static readonly string[] Names = ["x", "y", "", "X", "x ", "İ", "missing"];

    public static TheoryData<int> Widths => new() { 0, 1, 2, 3, 8, 33 };

    [Theory]
    [MemberData(nameof(Widths))]
    public void LookupNeed_IsTheOrderedFirstMatchScan(int width)
    {
        var random = new Random(4211 + width);
        var bindings = Enumerable.Range(0, width).Select(i => (Names[random.Next(Names.Length - 1)], Cell(i))).ToArray();
        foreach (var env in Shapes(bindings))
            foreach (var name in Names)
                Assert.Same(Linear(env, name), LookupNeed(env, name));
    }

    [Theory]
    [MemberData(nameof(Widths))]
    public void LookupVal_IsTheOrderedFirstMatchScan(int width)
    {
        var random = new Random(7759 + width);
        var bindings = Enumerable.Range(0, width).Select(i => (Names[random.Next(Names.Length - 1)], (Result)new Result.Atom(i))).ToArray();
        foreach (var env in Shapes(bindings))
            foreach (var name in Names)
                Assert.Same(Linear(env, name), LookupVal(env, name));
    }

    [Fact]
    public void Lookups_ShadowByPosition_TheFirstBindingWins()
    {
        // A callee's own bindings are prepended to the caller's (Evaluator.Concat): the inner one wins.
        var inner = Cell(1);
        var outer = Cell(2);
        IReadOnlyList<(string Name, NeedCell Cell)> needs = Evaluator.Concat<(string Name, NeedCell Cell)>([("x", inner)], [("x", outer), ("y", outer)]);
        Assert.Same(inner, LookupNeed(needs, "x"));
        Assert.Same(outer, LookupNeed(needs, "y"));
        Result first = new Result.Atom(1), second = new Result.Atom(2);
        IReadOnlyList<(string Name, Result Value)> values = Evaluator.Concat<(string Name, Result Value)>([("x", first)], [("x", second)]);
        Assert.Same(first, LookupVal(values, "x"));
        Assert.Null(LookupVal(values, "z"));
    }

    [Fact]
    public void Lookups_AllocateNothing_AtAnyTier()
    {
        // Measured from the very first calls, so the guard does not depend on tier-1 code, dynamic PGO
        // or escape analysis: an interface `foreach` boxes an enumerator per lookup without them.
        IReadOnlyList<(string Name, NeedCell Cell)> needs = Evaluator.Concat<(string Name, NeedCell Cell)>([("a", Cell(1)), ("b", Cell(2))], [("c", Cell(3))]);
        IReadOnlyList<(string Name, Result Value)> values = Evaluator.Concat<(string Name, Result Value)>([("a", new Result.Atom(1))], [("b", new Result.Atom(2))]);
        IReadOnlyList<(string Name, NeedCell Cell)> single = [("a", Cell(1))];
        IReadOnlyList<Property> properties = [new("P", new Algorithm.User(null, [], [], [], new OutputBundle([new Expr.Num(1)])), false), new("Q", new Algorithm.User(null, [], [], [], new OutputBundle([new Expr.Num(2)])), false)];
        var cache = new PropertyBindingIndexCache();
        var before = GC.GetAllocatedBytesForCurrentThread();
        var hits = 0;
        for (var i = 0; i < 1_000; i++)
        {
            if (LookupNeed(needs, "c") is not null) hits++;
            if (LookupNeed(single, "missing") is null) hits++;
            if (LookupVal(values, "b") is not null) hits++;
            if (cache.Lookup(properties, "Q") is not null) hits++;
        }
        var allocated = GC.GetAllocatedBytesForCurrentThread() - before;
        Assert.Equal(4_000, hits);
        Assert.Equal(0, allocated);
    }

    // ── Source programs: ordinary semantics and resource parity on the three engines ──────────────────────

    public static TheoryData<string, string, bool> Programs => new()
    {
        // The brief's core examples.
        { "Id(42)", "ok 42", true },
        { "Id(Box.G(5))", "ok 50", true },
        { "5.Add(1)", "ok 6", true },
        { "F(0) = 10\nF(1)", "err NoMatchingBranch", true },
        { "Loop(meta op) = op.Algorithm(op.Arguments*).while\nStep(0).Loop", "ok 3", false },
        { "Math.Abs(-3).repeat(2)", "ok 3", false },
        // Position shadowing: the callee's own binding precedes the caller's.
        { "F(x) = {\n  H(x) = x * 2\n  H(x + 1)\n}\nF(3)", "ok 8", true },
        { "F(x, y) = {\n  H(y) = x * 100 + y\n  H(x + y)\n}\nF(1, 2)", "ok 103", true },
        // The multi-name binder: distinct names, a repeated name (equal / unequal), a collecting tail.
        { "Add3(a, b, c) = a * 100 + b * 10 + c\nAdd3(1, 2, 3)", "ok 123", true },
        { "P(x, x) = x\nP(4, 4)", "ok 4", true },
        { "P(x, x) = x\nP(4, 5)", "err ArityMismatch", true },
        // The general binder can return zero or one name after inspecting literal patterns.
        { "P(1, 2) = 9\nP(1, 2)", "ok 9", true },
        { "P(1, y) = y\nP(1, 2)", "ok 2", true },
        { "C(a, *rest) = a + rest.count\nC(10, 2, 3, 4)", "ok 13", true },
        { "Only(*xs) = xs\nOnly(), Only", "ok ([], [])", true },
        { "Swap(a, b) = b, a\nSwap(1, 2)", "ok (2, 1)", true },
        // Member shadowing of an intrinsic and an extension through a parameter receiver.
        { "B = { Algorithm(x) = x + 7 }\nB.Algorithm(1)", "ok 8", true },
        { "U(n) = n.Add(n)\nU(4)", "ok 8", true },
        // Repeated execution of one written node and many distinct nodes.
        { "R(n) = if(n <= 0, 0, Id(Box.G(n)) + R(n - 1))\nR(5)", "ok 150", true },
        { "Id(Box.G(1)), Id(Inc(2)), 3.Add(4), Box.G(5)", "ok (10, 3, 7, 50)", true },
        // Loops: a named, a member, and a multi-state step.
        { "Fib(a, b, n) = b, a + b, n - 1, n > 0\nFib(0, 1, 10).while", "ok (55, 89, 0)", false },
        { "Box.Step(0).while", "ok 3", false },
        { "if(aflag(), Box.Step(0).while, 0)", "ok 3", false },
    };

    [Theory]
    [MemberData(nameof(Programs))]
    public async Task Program_HasThePinnedOutcome_AndOneResourceProfile_OnAllEngines(string source, string expected, bool plainToo)
    {
        foreach (var plain in plainToo ? new[] { true, false } : [false])
        {
            var c = new InvocationRouteCorpus.Case("PERF-ORD-1", source, Plain: plain);
            var generic = await InvocationRouteCorpus.Observe(c, 0);
            if (expected.StartsWith("ok ", StringComparison.Ordinal))
                Assert.Equal(expected, generic.Outcome);
            else
                Assert.StartsWith(expected + " | ", generic.Outcome, StringComparison.Ordinal);
            var optimized = await InvocationRouteCorpus.Observe(c, 1);
            var asynchronous = await InvocationRouteCorpus.Observe(c, 2);
            if (source.Contains("aflag()", StringComparison.Ordinal))
                Assert.True(asynchronous.Suspensions > 0);
            Assert.Equal(generic.Semantic, optimized.Semantic);
            Assert.Equal(generic.Semantic, asynchronous.Semantic);
            Assert.Equal(generic.Plans, optimized.Plans);
            Assert.Equal(generic.Plans, asynchronous.Plans);
            Assert.Equal(generic.Formations, asynchronous.Formations);
        }
    }
}
