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
///
/// <para>A list is evaluated on demand (issue #204). An observation can use the whole value the
/// run already built, assemble it from cached one-level forms, or — for a list whose cardinality
/// the run settled — from the completed positions it read one at a time
/// (<see cref="PropertyObservationPositionReadTests"/>). A list read too little, cycles and call
/// references all make the value unavailable to the observer.</para>
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
            Meta + "R = Capture(Square(5))\nL = [[R], 1]\nS = (L, R), 2\nM = [S, [L]]\nPlain = [1, [2]]\ncontains(M, 0), contains(Plain, 0)",
            // In publication order: M is published unread; reading it whole evaluates S, whose
            // sequence evaluates L and R.
            "M=<withheld>#1; L=<withheld>#1; R=<withheld>#1; S=<withheld>#2; Plain=[1, [2]]#1"
        },
        {
            "shared DAG",
            Meta + "R = Capture(Square(5))\nShared = [R, R]\nA = [Shared, Shared]\nB = [Shared]\ncontains(A, 0), contains(B, 0)",
            "A=<withheld>#1; Shared=<withheld>#1; R=<withheld>#1; B=<withheld>#1"
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
                Assert.False(Evaluator.ContainsCallReference(observation.Value, new Dictionary<Result, bool>(ReferenceEqualityComparer.Instance)));
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
            Whole(x) = if(contains(x, 0), 1, 0)
            count(Clean) + count(Dirty) + count(First) + count(Later) + Whole(Clean) + Whole(Dirty) + Whole(First) + Whole(Later)
            """;

        var result = Run(source);

        Assert.Equal("7", result.ToDisplayString());
        // In publication order: the four lists are published unread by their `count`; reading Clean whole
        // then evaluates Big, and reading Dirty whole evaluates R.
        var big = "[" + string.Join(", ", Enumerable.Range(1, 100)) + "]";
        Assert.Equal(
            $"Clean=[{big}, 1]#1; Dirty=<withheld>#1; First=<withheld>#1; Later=<withheld>#1; Big={big}#1; R=<withheld>#1",
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
        var result = Assert.IsType<RunResult.Success>(Run("Big = range(1, 1000)\nTwice = [Big, Big]\nBig.count + Twice.count + if(contains(Twice, 0), 1, 0)"));
        var big = Single(result, "Big").Value!;
        var twice = (Result.ListValue)Single(result, "Twice").Value!;

        Assert.Same(big, twice.Items[0]);
        Assert.Same(big, twice.Items[1]);
    }

    // ── Remembered one-level forms: shared, and never followed in a circle ────────────────────

    // An async host operation selects the async evaluator even when the program never calls it.
    private static HostOperations AsyncOperations => new TickLog().Operations(suspending: true);

    /// <summary>
    /// <c>L = [L]</c> builds a list that holds itself, and <c>L.skip(1)</c> reads its one position —
    /// the list, not its contents — and drops it. The one-level form the run remembered for
    /// <c>L</c> therefore holds <c>L</c> again: it has no finite concrete form. The snapshot follows
    /// remembered forms only while they lead somewhere new, so the run completes with its ordinary
    /// output and <c>L</c> is withheld, with its declaration and emitted count intact. (Before the
    /// active-path check the snapshot walked that form forever, after the run had its result.)
    /// </summary>
    [Fact]
    public async Task ASelfContainingListReadAtOneLevel_IsWithheld_AndTheRunCompletesWithItsOrdinaryOutput()
    {
        const string source = "L = [L]\nL.skip(1)";
        var unobserved = KatLangEngine.Run(source);
        var operations = AsyncOperations;
        var unobservedAsync = await KatLangEngine.RunAsync(source, Options(observe: false, operations));
        var observed = Run(source);
        var observedAsync = await RunAsync(source, operations);

        Assert.Null(unobserved.PropertyObservations);
        Assert.Null(unobservedAsync.PropertyObservations);
        Assert.Equal(Outcome(unobservedAsync), Outcome(observedAsync));
        foreach (var result in new[] { observed, observedAsync })
        {
            var success = Assert.IsType<RunResult.Success>(result);
            Assert.Equal("[]", success.ToDisplayString());
            Assert.Equal(Outcome(unobserved), Outcome(result));

            var observation = Assert.Single(result.PropertyObservations!);
            Assert.Equal("L", observation.Name);
            Assert.Equal(PropertyValueStatus.Withheld, observation.Status);
            Assert.Null(observation.Value);
            Assert.Equal(1, observation.EmittedCount);
            Assert.Equal(new SourceSpan(1, 1, 1, 2), observation.DeclarationSpan);
            var refused = Assert.Throws<ArgumentException>(() => result.RenderPropertyValue(observation));
            Assert.Equal("observation", refused.ParamName);
        }
    }

    /// <summary>
    /// Every way a remembered form can lead back to a list the snapshot is inside: through a second
    /// list, below an acyclic parent, inside a sequence, and after an acyclic first item. Each run
    /// completes with the output it has unobserved, on both engine routes, and every property whose
    /// value reaches the cycle is withheld.
    /// </summary>
    public static TheoryData<string, string, string> CyclicForms => new()
    {
        { "two lists", "A = [B]\nB = [A]\nA.skip(1), B.skip(1)", "A=<withheld>#1; B=<withheld>#1" },
        { "below a parent", "L = [L]\nW = [L]\nL.skip(1), W.skip(1)", "L=<withheld>#1; W=<withheld>#1" },
        { "inside a sequence", "L = [L]\nS = L, 1\nL.skip(1), S.count", "L=<withheld>#1; S=<withheld>#2" },
        { "after a plain item", "L = [1 + 1, L]\nL.skip(2)", "L=<withheld>#1" },
        { "three lists", "A = [B]\nB = [C]\nC = [A]\nA.skip(1), B.skip(1), C.skip(1)", "A=<withheld>#1; B=<withheld>#1; C=<withheld>#1" },
    };

    [Theory]
    [MemberData(nameof(CyclicForms))]
    public async Task EveryCycleOfRememberedForms_IsWithheld_AndTheOrdinaryOutcomeIsUnchanged(string label, string source, string expected)
    {
        _ = label;
        var unobserved = KatLangEngine.Run(source);
        var observed = Run(source);
        var observedAsync = await RunAsync(source, AsyncOperations);

        Assert.IsType<RunResult.Success>(unobserved);
        Assert.Equal(Outcome(unobserved), Outcome(observed));
        Assert.Equal(Outcome(unobserved), Outcome(observedAsync));
        Assert.Equal(expected, Describe(observed));
        Assert.Equal(expected, Describe(observedAsync));
        Assert.All(observed.PropertyObservations!, static o => Assert.Null(o.Value));
    }

    /// <summary>
    /// A list that holds itself and is demanded as the run's output is the ordinary demand cycle,
    /// observed or not; the list was published when it was built and has no concrete form.
    /// </summary>
    [Fact]
    public async Task ASelfContainingListDemandedAsOutput_StaysADemandCycle_AndIsWithheld()
    {
        const string source = "L = [L]\nL";
        var unobserved = KatLangEngine.Run(source);
        var observed = Run(source);
        var observedAsync = await RunAsync(source, AsyncOperations);

        var failure = Assert.IsType<RunResult.EvalFailure>(unobserved);
        Assert.Equal(KatLangErrorCode.DemandCycle, Assert.Single(failure.Errors).Code);
        Assert.Equal(Outcome(unobserved), Outcome(observed));
        Assert.Equal(Outcome(unobserved), Outcome(observedAsync));
        Assert.Equal("L=<withheld>#1", Describe(observed));
        Assert.Equal("L=<withheld>#1", Describe(observedAsync));
    }

    /// <summary>
    /// Each list has only its one-level form. Replacing the lazy leaf inside <c>C</c> requires
    /// rebuilding <c>C</c>, so reference equality inside <c>P</c> checks reuse of the completed
    /// child snapshot even when the original one-level form cannot be returned as-is.
    /// </summary>
    [Fact]
    public async Task ASharedChildReachedTwiceThroughOneLevelForms_IsAvailable_AndStaysShared()
    {
        const string source = "Leaf = [1 + 1, 3]\nC = [Leaf]\nP = [C, C]\nLeaf.sum, C.skip(1), P.skip(2)";
        var observed = Run(source);
        var observedAsync = await RunAsync(source, AsyncOperations);

        foreach (var result in new[] { observed, observedAsync })
        {
            Assert.Equal("5\n[]\n[]", Assert.IsType<RunResult.Success>(result).ToDisplayString().ReplaceLineEndings("\n"));
            Assert.Equal("Leaf=[2, 3]#1; C=[[2, 3]]#1; P=[[[2, 3]], [[2, 3]]]#1", Describe(result));
            var parent = Single(result, "P");
            Assert.Equal(PropertyValueStatus.Available, parent.Status);

            var positions = Assert.IsType<Result.ListValue>(parent.Value).Items;
            Assert.Equal(2, positions.Count);
            Assert.Same(positions[0], positions[1]);
            var leaf = Assert.Single(Assert.IsType<Result.ListValue>(positions[0]).Items);
            Assert.Same(Single(result, "Leaf").Value, leaf);
        }
    }

    /// <summary>
    /// A diamond of one-level forms: <c>D</c> is reached through <c>A</c> and through <c>B</c>. Its
    /// frame has completed — it is off the active path and in the completed memo — when the second
    /// parent reaches it, so sharing is never mistaken for a cycle.
    /// </summary>
    [Fact]
    public async Task AChildSharedByTwoParents_IsNotMistakenForACycle()
    {
        const string source = "D = [1 + 1]\nA = [D]\nB = [D]\nP = [A, B]\nD.sum, A.skip(1), B.skip(1), P.skip(2)";
        var observed = Run(source);
        var observedAsync = await RunAsync(source, AsyncOperations);

        foreach (var result in new[] { observed, observedAsync })
        {
            Assert.Equal("D=[2]#1; A=[[2]]#1; B=[[2]]#1; P=[[[2]], [[2]]]#1", Describe(result));
            var top = Assert.IsType<Result.ListValue>(Single(result, "P").Value).Items;
            var throughA = Assert.IsType<Result.ListValue>(top[0]).Items[0];
            var throughB = Assert.IsType<Result.ListValue>(top[1]).Items[0];
            Assert.Same(throughA, throughB);
            Assert.Same(Single(result, "D").Value, throughA);
        }
    }

    /// <summary>
    /// A cyclic observation costs only itself: an independent property of the same run is still
    /// snapshotted and shown, before and after the withheld one.
    /// </summary>
    [Fact]
    public async Task ACyclicObservationAndAnIndependentAvailableOne_AppearInTheSameRun()
    {
        const string source = "First = [1 + 1, 3]\nL = [L]\nLast = [4 + 1]\nFirst.sum, L.skip(1), Last.sum";
        var unobserved = KatLangEngine.Run(source);
        var observed = Run(source);
        var observedAsync = await RunAsync(source, AsyncOperations);

        foreach (var result in new[] { observed, observedAsync })
        {
            Assert.Equal("5\n[]\n5", Assert.IsType<RunResult.Success>(result).ToDisplayString().ReplaceLineEndings("\n"));
            Assert.Equal(Outcome(unobserved), Outcome(result));
            Assert.Equal("First=[2, 3]#1; L=<withheld>#1; Last=[5]#1", Describe(result));
            Assert.Equal(PropertyValueStatus.Available, Single(result, "First").Status);
            Assert.Equal(PropertyValueStatus.Withheld, Single(result, "L").Status);
            Assert.Null(Single(result, "L").Value);
            Assert.Equal(PropertyValueStatus.Available, Single(result, "Last").Status);
        }
    }
}
