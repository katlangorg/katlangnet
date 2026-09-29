using System.Collections;
using System.Reflection;
using Xunit.Abstractions;

namespace KatLang.Tests;

public class RepeatedNameAdversarialReviewTests(ITestOutputHelper output)
{
    [Theory]
    [InlineData("P(*x, x) = x")]
    [InlineData("P(x, *x) = x")]
    [InlineData("P(x, *x, x) = x")]
    [InlineData("P(*x, (x)) = x")]
    public void CollectorsCannotShareANameWithOrdinaryCaptures(string declaration)
    {
        Assert.Contains(Parser.Parse(declaration + "\n0").Diagnostics,
            diagnostic => diagnostic.Code == DiagnosticCode.InvalidCollectingBinding);
    }

    [Theory]
    [InlineData("P(Bad, Missing, 7)", "err BadIndex:")]
    [InlineData("P(Missing, Bad, 7)", "err DivisionByZero:")]
    public async Task RetainedFailures_KeepTheEstablishedSuffixBeforeCollectorOrder(string call, string expected)
    {
        var result = await RepeatedNameConstraintTests.OnEveryRouteAsync(
            "Bad = trace(1) / 0\nMissing = [trace(2)]:5\nP(*r, x, x) = x\n" + call);
        Assert.StartsWith(expected, result.Outcome);
        Assert.Equal(call == "P(Bad, Missing, 7)" ? ["trace(1)", "trace(2)"] : ["trace(2)", "trace(1)"], result.HostCalls);
    }

    [Fact]
    public async Task PrefixVerdict_PrecedesASuffixRepeatedNamesRetainedFailure()
    {
        var result = await RepeatedNameConstraintTests.OnEveryRouteAsync(
            "Bad = trace(1) / 0\nP(x, x, *r, f, f) = 0\nP(1, 2, Bad, 7)");
        Assert.StartsWith("err ArityMismatch:", result.Outcome);
        Assert.Equal(["trace(1)"], result.HostCalls);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public async Task UniqueValuelessCaptures_AreStillLegalBesideARepeatedName(bool collector)
    {
        var names = Enumerable.Range(0, 32).Select(i => $"a{i}").ToList();
        if (collector)
            names.Insert(16, "*rest");
        names.AddRange(["x", "x"]);
        var source = $"Inc(y) = y\nP({string.Join(", ", names)}) = x\n"
            + $"P({string.Join(", ", Enumerable.Repeat("Inc", 32))}, 7, 7)";
        Assert.Equal("ok 7", (await RepeatedNameConstraintTests.OnEveryRouteAsync(source)).Outcome);
    }

    [Theory]
    [InlineData("P(Pick, 10)")]
    [InlineData("P(10, Pick)")]
    [InlineData("Same(Pick)")]
    [InlineData("Wrap(Pick, 10)")]
    public async Task RepeatedNames_CannotHealASeededFailure(string call)
    {
        const string source = "Pick = [10, 20]:(trace(randomInt(0, 3)))\nP(x, x) = x\n"
            + "Same(a) = P(a, a)\nWrap(a, b) = { Inner = P(a, b)\nInner }\n";
        var result = await RepeatedNameConstraintTests.OnEveryRouteAsync(source + call, seed: 4);
        Assert.StartsWith("err BadIndex:", result.Outcome);
        Assert.Equal(["trace(2)"], result.HostCalls);
    }

    [Theory]
    [InlineData("P(Bad, 7)", "err DivisionByZero:", new[] { "tick#1" })]
    [InlineData("P(7, Bad)", "err DivisionByZero:", new[] { "tick#1" })]
    [InlineData("Same(Bad)", "err DivisionByZero:", new[] { "tick#1" })]
    [InlineData("P(Each, 7)", "err DivisionByZero:", new[] { "trace(1)" })]
    [InlineData("P(7, Each)", "err DivisionByZero:", new[] { "trace(1)" })]
    [InlineData("Same(Each)", "err DivisionByZero:", new[] { "trace(1)" })]
    public async Task RetainedFailures_FromStatefulBodiesAndCallbacks_AreNotRetried(
        string call, string prefix, string[] effects)
    {
        const string source = "Bad = if(tick() == 1, 1 / 0, 7)\n"
            + "Each = map([1, 2], {trace(x) / 0})\nP(x, x) = 0\nSame(a) = P(a, a)\n";
        var result = await RepeatedNameConstraintTests.OnEveryRouteAsync(source + call);
        Assert.StartsWith(prefix, result.Outcome);
        Assert.Equal(effects, result.HostCalls);
    }

    [Fact]
    public async Task EqualValues_DoNotEraseIndependentEffectsOrCallableIdentity()
    {
        var explicitCalls = await RepeatedNameConstraintTests.OnEveryRouteAsync(
            "A = trace(randomInt(0, 3))\nP(x, x) = x\nP(A(), A())", seed: 4);
        Assert.StartsWith("err ArityMismatch:", explicitCalls.Outcome);
        Assert.Equal(["trace(2)", "trace(0)"], explicitCalls.HostCalls);

        var cached = await RepeatedNameConstraintTests.OnEveryRouteAsync(
            "A = trace(randomInt(0, 3))\nP(x, x) = x\nP(A, A), randomInt(0, 3)", seed: 4);
        Assert.Equal("ok S[2, 0]", cached.Outcome);
        Assert.Equal(["trace(2)"], cached.HostCalls);

        var different = await RepeatedNameConstraintTests.OnEveryRouteAsync(
            "A = trace(5)\nB = trace(5)\nP(x, x) = x\nP(A, B)");
        Assert.StartsWith("err TypeMismatch:", different.Outcome);
        Assert.Equal(["trace(5)", "trace(5)"], different.HostCalls);
    }

    [Theory]
    [InlineData(64)]
    [InlineData(2048)]
    public void RepetitionDetection_IsIterativeLinearAndCached(int depth)
    {
        var lists = new List<CountingPatterns>();
        ParameterPattern nested = new CaptureParameterPattern("x");
        for (var i = 0; i < depth; i++)
        {
            var children = new CountingPatterns([nested]);
            lists.Add(children);
            nested = new SequenceValueParameterPattern(children);
        }
        var signature = CallableSignature.FromAlgorithm("P",
            new Algorithm.User(null, [new CaptureParameterPattern("x"), nested], [], [], []));
        Assert.Equal("x", signature.RepeatedParameterName);
        var reads = lists.Sum(list => list.Reads);
        Assert.InRange(reads, depth, depth * 3);
        for (var i = 0; i < 100; i++)
            Assert.Equal("x", signature.RepeatedParameterName);
        Assert.Equal(reads, lists.Sum(list => list.Reads));
    }

    [Theory]
    [InlineData("P(((x)), x) = x")]
    [InlineData("P(x, (a, x)) = a")]
    [InlineData("P((x, a), (x, b)) = a + b")]
    public void AdditionalNestedShapes_AreRefusedAndExplicitCallsRemainLegal(string declaration)
    {
        var parsed = Parser.Parse(declaration + "\nAlias = P\n0");
        Assert.Equal(DiagnosticCode.RepeatedParameterNotForwardable, Assert.Single(parsed.Diagnostics).Code);
        var alias = Assert.IsType<Algorithm.User>(parsed.Root.Properties.Single(p => p.Name == "Alias").Value);
        Assert.Empty(alias.Params);
        SourceProvenance.ParseValid(declaration + "\nW(a, b) = P(a, b)\n0");
    }

    // Count input visits, not elapsed time. These unrelated failed callable slots are legal
    // higher-order bindings; a repeated name at the end must not rescan them once per slot.
    [Theory]
    [InlineData(64, false)]
    [InlineData(256, false)]
    [InlineData(64, true)]
    [InlineData(256, true)]
    public void ValuelessUnrelatedCaptures_InspectThePatternLevelOnlyLinearly(int width, bool collector)
    {
        var items = Enumerable.Range(0, width)
            .Select(i => (ParameterPattern)new CaptureParameterPattern($"a{i}")).ToList();
        if (collector)
            items.Insert(width / 2, new CaptureParameterPattern("rest", Kind: ParameterKind.Collecting));
        items.Add(new CaptureParameterPattern("x"));
        items.Add(new CaptureParameterPattern("x"));
        var patterns = new CountingPatterns(items);

        var inputType = typeof(Evaluator).GetNestedType("ParameterPatternInput", BindingFlags.NonPublic)!;
        var inputs = Array.CreateInstance(inputType, width + 2);
        var callable = new Algorithm.User(null, Algorithm.NormalParameters(["y"]), [], [], [new Expr.Param("y")]);
        for (var i = 0; i < width + 2; i++)
        {
            inputs.SetValue(Activator.CreateInstance(inputType,
                [i < width ? null : new Result.Atom(7), callable,
                    i < width ? new EvalError.DivByZero() : null]), i);
        }

        var bind = typeof(Evaluator).GetMethod("BindParameterPatternList", BindingFlags.Static | BindingFlags.NonPublic)!;
        object?[] arguments = [patterns, inputs, Evaluator.EvalCtx.Empty, true,
            (Func<int, int, EvalError>)((required, actual) => new EvalError.ArityMismatch(required, actual))];
        _ = bind.Invoke(null, arguments);
        patterns.Reset();
        var allocatedBefore = GC.GetAllocatedBytesForCurrentThread();
        var outcome = bind.Invoke(null, arguments)!;
        var allocated = GC.GetAllocatedBytesForCurrentThread() - allocatedBefore;
        output.WriteLine($"{items.Count} patterns, collector={collector}: {patterns.Reads} visits, {allocated} allocated bytes.");
        Assert.True((bool)outcome.GetType().GetProperty("IsOk")!.GetValue(outcome)!);
        Assert.True(patterns.Reads <= 20 * items.Count,
            $"{items.Count} patterns took {patterns.Reads} visits; repeated-name requirements must be indexed once per level.");
        Assert.InRange(allocated, 0, 4096L * items.Count + 65536);
    }

    private sealed class CountingPatterns(IReadOnlyList<ParameterPattern> items) : IReadOnlyList<ParameterPattern>
    {
        public int Reads { get; private set; }
        public void Reset() => Reads = 0;
        public int Count => items.Count;
        public ParameterPattern this[int index] { get { Reads++; return items[index]; } }
        public IEnumerator<ParameterPattern> GetEnumerator()
        {
            for (var i = 0; i < Count; i++)
                yield return this[i];
        }
        IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();
    }
}
