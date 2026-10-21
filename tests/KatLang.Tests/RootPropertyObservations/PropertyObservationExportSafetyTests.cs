using System.Reflection;
using KatLang.Evaluation.Caching;
using static KatLang.Tests.RootPropertyObservations.PropertyObservationTestSupport;

namespace KatLang.Tests.RootPropertyObservations;

/// <summary>
/// The observation snapshot is a NEW way for values to leave a run, so it keeps the run-result
/// boundary (CallReference S1, J4): a published value that contains a call reference anywhere in
/// its sequence/list structure is <see cref="PropertyValueStatus.Withheld"/> — classified by the
/// existing context-free predicate (<see cref="Evaluator.ContainsCallReference(Result, Dictionary{Result, bool})"/>) after the run —
/// and never exposed, while the ordinary outcome is exactly the unobserved run's. The public
/// snapshot types hold nothing but names, spans, counts, statuses, and export-safe values.
/// </summary>
public class PropertyObservationExportSafetyTests
{
    private const string Meta = "Square(x) = x * x\nCapture(meta operation) = operation\n";

    public static TheoryData<string, string, string> ReferenceCases => new()
    {
        { "direct", Meta + "R = Capture(Square(5))\nR.Invoke()", "R=<withheld>#1" },
        { "list", Meta + "R = Capture(Square(5))\nL = [R, 1]\nR.Invoke() + count(L)", "R=<withheld>#1; L=<withheld>#1" },
        { "sequence", Meta + "R = Capture(Square(5))\nS = R, 2\ncount(S)", "R=<withheld>#1; S=<withheld>#2" },
        {
            "mixed nesting",
            Meta + "R = Capture(Square(5))\nL = [[R], 1]\nS = (L, R), 2\nM = [S, [L]]\nPlain = [1, [2]]\ncount(M) + count(Plain)",
            "R=<withheld>#1; L=<withheld>#1; S=<withheld>#2; M=<withheld>#1; Plain=[1, [2]]#1"
        },
        {
            "shared DAG",
            Meta + "R = Capture(Square(5))\nShared = [R, R]\nA = [Shared, Shared]\nB = [Shared]\ncount(A) + count(B)",
            "R=<withheld>#1; Shared=<withheld>#1; A=<withheld>#1; B=<withheld>#1"
        },
        { "before failure", Meta + "R = Capture(Square(5))\nOk = 3\nBoom = 1 / 0\nR.Invoke() + Ok + Boom", "R=<withheld>#1; Ok=3#1" },
        { "refused output", Meta + "R = Capture(Square(5))\nR", "R=<withheld>#1" },
    };

    [Theory]
    [MemberData(nameof(ReferenceCases))]
    public async Task CallReferenceValues_AreWithheld_AndTheOrdinaryOutcomeIsUnchanged(string label, string source, string expected)
    {
        _ = label;
        AssertLegal(source);
        var unobserved = KatLangEngine.Run(source);
        var observed = Run(source);
        var observedAsync = await RunAsync(source);

        Assert.Equal(Outcome(unobserved), Outcome(observed));
        Assert.Equal(Outcome(unobserved), Outcome(observedAsync));
        Assert.Equal(expected, Describe(observed));
        Assert.Equal(expected, Describe(observedAsync));

        foreach (var observation in observed.PropertyObservations!)
        {
            if (observation.Status == PropertyValueStatus.Withheld)
            {
                Assert.Null(observation.Value);
                var refused = Assert.Throws<ArgumentException>(() => observed.RenderPropertyValue(observation));
                Assert.Equal("observation", refused.ParamName);
            }
            else
            {
                Assert.NotNull(observation.Value);
                Assert.False(Evaluator.ContainsCallReference(observation.Value));
            }
        }
    }

    [Fact]
    public void SnapshotMemo_NeverProvesAStructureCleanThatAFailedScanEntered()
    {
        // Dirty = [[R], 1] is scanned before First = Dirty.first, which IS the inner [R] that the
        // failed scan expanded on its way to R. The unfinished path must be memoized as forbidden,
        // never clean, so First must still be withheld; Clean shares Big with a later dirty root
        // and stays available without hiding that root's reference.
        const string source = Meta + """
            R = Capture(Square(5))
            Big = range(1, 100)
            Clean = [Big, 1]
            Dirty = [[R], 1]
            First = Dirty.first
            Later = [Big, R]
            count(Clean) + count(Dirty) + count(First) + count(Later)
            """;

        var result = Run(source);

        Assert.Equal("7", result.ToDisplayString());
        Assert.Equal(
            "Big=[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100]#1; "
                + "Clean=[[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100], 1]#1; "
                + "R=<withheld>#1; Dirty=<withheld>#1; First=<withheld>#1; Later=<withheld>#1",
            Describe(result));
        var clean = (Result.ListValue)Single(result, "Clean").Value!;
        Assert.Same(Single(result, "Big").Value, clean.Items[0]);
    }

    [Fact]
    public void SnapshotMemo_ReusesForbiddenGraphs_AndCleanPrefixesOfFailedScans()
    {
        var reference = new Result.CallReference(new Evaluator.InvocationPlan(Evaluator.EvalCtx.Empty, []));
        var clean = new Result.ListValue(Enumerable.Range(0, 1000).Select(static n => (Result)new Result.Atom(n)).ToArray());
        var unvisited = new Result.ListValue([new Result.Atom(9)]);
        var dirty = new Result.ListValue([clean, reference, unvisited]);
        var completed = new Dictionary<Result, bool>(ReferenceEqualityComparer.Instance);

        Assert.True(Evaluator.ContainsCallReference(dirty, completed));
        Assert.True(completed[dirty]);
        Assert.False(completed[clean]);
        Assert.False(completed.ContainsKey(unvisited));
        Assert.True(Evaluator.ContainsCallReference(dirty, completed));
        Assert.Equal(2, completed.Count);

        // A different root can reuse both the known forbidden child and the known clean prefix.
        var wrapped = new Result.ListValue([dirty]);
        Assert.True(Evaluator.ContainsCallReference(wrapped, completed));
        Assert.True(completed[wrapped]);
        var anotherDirty = new Result.SequenceValue([clean, reference]);
        Assert.True(Evaluator.ContainsCallReference(anotherDirty, completed));
        Assert.True(completed[anotherDirty]);
        Assert.False(Evaluator.ContainsCallReference(unvisited, completed));
        Assert.False(completed[unvisited]);
    }

    [Fact]
    public void SnapshotMemo_ClassifiesDeepSharedGraphs_WithoutRecursionOrLosingVerdicts()
    {
        const int depth = 2048;
        var reference = new Result.CallReference(new Evaluator.InvocationPlan(Evaluator.EvalCtx.Empty, []));
        var clean = new Result.ListValue([new Result.Atom(1), new Result.Atom(2)]);
        Result graph = reference;
        for (var i = 0; i < depth; i++)
            graph = i % 2 == 0 ? new Result.ListValue([clean, graph]) : new Result.SequenceValue([clean, graph]);
        var completed = new Dictionary<Result, bool>(ReferenceEqualityComparer.Instance);

        Assert.True(Evaluator.ContainsCallReference(graph, completed));
        Assert.Equal(depth + 1, completed.Count);
        Assert.False(completed[clean]);
        Assert.Equal(depth, completed.Values.Count(static containsReference => containsReference));
        Assert.True(Evaluator.ContainsCallReference(graph, completed));
        Assert.False(Evaluator.ContainsCallReference(clean, completed));
    }

    [Fact]
    public void RefusedOutput_StaysTheOrdinaryExportFailure()
    {
        var observed = Run(Meta + "R = Capture(Square(5))\nR");
        var failure = Assert.IsType<RunResult.EvalFailure>(observed);
        Assert.Equal(KatLangErrorCode.TypeMismatch, Assert.Single(failure.Errors).Code);
    }

    [Fact]
    public void PublicSnapshotTypes_HoldOnlyNamesSpansCountsStatusesAndValues()
    {
        // No cache key, context, budget, environment, plan, cell, or sink can be reachable from a
        // snapshot: the fields of its types admit none.
        static IEnumerable<Type> FieldTypes(Type type)
            => type.GetFields(BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic).Select(static f => f.FieldType);

        Assert.Equal([typeof(PropertyValueObservation[])], FieldTypes(typeof(PropertyObservations)));
        Assert.Equal(
            new[] { typeof(int), typeof(PropertyValueStatus), typeof(Result), typeof(SourceSpan), typeof(string) }.Select(static t => t.FullName).Order(),
            FieldTypes(typeof(PropertyValueObservation)).Select(static t => t.FullName).Order());
    }

    [Fact]
    public void Complete_ReleasesTheRawRecords()
    {
        var parsed = Parser.Parse(Meta + "R = Capture(Square(5))\nL = [R]\nR.Invoke() + count(L)");
        Assert.False(parsed.HasErrors);
        var sink = new RootPropertyObservationSink(parsed.Root);
        var (result, _) = Evaluator.RunCountedObserved(
            new Expr.AlgorithmExpr(parsed.Root),
            zeroArgPropertyResultCache: new RunScopedZeroArgPropertyResultCache(sink));
        Assert.False(result.IsError, result.ToString());

        var records = (System.Collections.ICollection)typeof(RootPropertyObservationSink)
            .GetField("_records", BindingFlags.Instance | BindingFlags.NonPublic)!
            .GetValue(sink)!;
        Assert.Equal(2, records.Count);

        var snapshot = sink.Complete();

        Assert.Empty(records);
        Assert.All(snapshot, o => Assert.Equal(PropertyValueStatus.Withheld, o.Status));
        Assert.All(snapshot, o => Assert.Null(o.Value));
    }

    [Fact]
    public void ReferenceFreeValues_AreSharedNotCopied()
    {
        var result = Assert.IsType<RunResult.Success>(Run("Big = range(1, 1000)\nTwice = [Big, Big]\nBig.count + Twice.count"));
        var big = Single(result, "Big").Value!;
        var twice = (Result.ListValue)Single(result, "Twice").Value!;

        Assert.Same(big, twice.Items[0]);
        Assert.Same(big, twice.Items[1]);
    }
}
