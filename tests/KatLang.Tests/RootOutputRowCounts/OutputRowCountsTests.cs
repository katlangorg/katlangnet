using System.Reflection;
using KatLang.Evaluation;
using KatLang.Evaluation.Caching;
using static KatLang.Tests.RootOutputRowCounts.OutputRowCountsTestSupport;

namespace KatLang.Tests.RootOutputRowCounts;

/// <summary>
/// <see cref="RunResult.Success.OutputRowCounts"/>: how many entries of
/// <see cref="RunResult.Success.OutputRows"/> each written root output row produced. The table is
/// the member's contract, checked on the synchronous engine, the asynchronous engine, the engine's
/// async twin (an asynchronous host operation is configured, so the twin evaluates the program
/// whether or not it is called), both evaluator funnels the engines drive, and the observed
/// harness routes. The remaining tests pin the slices a host reads, real suspension, concurrent
/// runs, module-loaded spreads, copies, property observation, and the variants that have no such
/// member.
/// </summary>
public class OutputRowCountsTests
{
    private const string SixSource =
        "Six(x)* = x, x + 1, x + 2, x + 3, x + 4, x + 5\nSix(10)\n''\nSix(20)";

    /// <summary>Program, the elaborated root's row kinds, the output row count, the counts.</summary>
    public static TheoryData<string, string, int, int[]> Table => new()
    {
        { "A = 1, 2, 3\nA", "plain", 1, new[] { 1 } },
        { "A = 1, 2, 3\nA\n4", "plain, plain", 2, new[] { 1, 1 } },
        { "E = ()\nA = 1, 2\nE*\nA", "spread, plain", 1, new[] { 0, 1 } },
        { "E = ()\nE*", "spread", 0, new[] { 0 } },
        { "Point(x, y)* = x, y\nPoint(1, 2)\n''\nPoint(3, 4)", "spread, plain, spread", 5, new[] { 2, 1, 2 } },
        { "[1, 2]*", "spread", 2, new[] { 2 } },
        { "A = 1, 2\n{ A* }", "plain", 1, new[] { 1 } },
        { "F(x)* = x\nF(5)\nF(6)", "spread, spread", 2, new[] { 1, 1 } },
        { "Fib(a, b)* = b, a + b\nStep(a, b) = Fib(a, b)\nStep(0, 1).repeat(10)", "plain", 1, new[] { 1 } },
        { SixSource, "spread, plain, spread", 13, new[] { 6, 1, 6 } },
    };

    /// <summary>
    /// Boundary controls: adjacent zero-width spreads, leading and trailing zero contributions, a
    /// program of zero-width spreads only, and a spread that supplies one structured value.
    /// </summary>
    public static TheoryData<string, string, int, int[]> Boundaries => new()
    {
        { "E = ()\nV = 5\nE*\nE*\nV\nE*", "spread, spread, plain, spread", 1, new[] { 0, 0, 1, 0 } },
        { "E = ()\nA = 1, 2\nE*\nA*\nE*", "spread, spread, spread", 2, new[] { 0, 2, 0 } },
        { "E = ()\nE*\nE*", "spread, spread", 0, new[] { 0, 0 } },
        { "E = ()\nL = [[1, 2]]\nE*\nL*\nE*", "spread, spread, spread", 1, new[] { 0, 1, 0 } },
        { "E = ()\nS = ''\nL = []\nS\nE\nL\nE*", "plain, plain, plain, spread", 3, new[] { 1, 1, 1, 0 } },
    };

    private static RunResult.Success AssertRow(RunResult result, string kinds, int outputRows, int[] counts)
    {
        var success = Assert.IsType<RunResult.Success>(result);
        Assert.Equal(kinds, RowKinds(success.Root));
        Assert.Equal(outputRows, success.OutputRows.Count);
        Assert.Equal(counts, success.OutputRowCounts);
        AssertPartition(success);
        return success;
    }

    [Theory]
    [MemberData(nameof(Table))]
    [MemberData(nameof(Boundaries))]
    public async Task EveryRow_HasItsCounts_OnTheEngines(string source, string kinds, int outputRows, int[] counts)
    {
        AssertRow(KatLangEngine.Run(source), kinds, outputRows, counts);
        AssertRow(await KatLangEngine.RunAsync(source), kinds, outputRows, counts);

        // An asynchronous host operation in the configuration selects the async twin for the
        // whole run, called or not, so the twin's row loop is the one that records here.
        var pause = new Pause();
        var twinOptions = new RunOptions { HostOperations = pause.Operations() };
        AssertRow(await KatLangEngine.RunAsync(source, twinOptions), kinds, outputRows, counts);
    }

    [Theory]
    [MemberData(nameof(Table))]
    [MemberData(nameof(Boundaries))]
    public async Task EveryRow_HasItsSlotCounts_OnTheEvaluatorFunnels_AndTheForcedTwin(
        string source, string kinds, int outputRows, int[] counts)
    {
        var parsed = Parser.Parse(source);
        Assert.False(parsed.HasErrors, string.Join("\n", parsed.Diagnostics.Select(static d => d.Message)));
        Assert.Equal(kinds, RowKinds(parsed.Root));
        var program = new Expr.AlgorithmExpr(parsed.Root);

        // The funnels KatLangEngine.Run and RunAsync evaluate through. In these programs every
        // stored slot is one output row, so the recorded slot counts are the row counts.
        var sync = Evaluator.RunCountedWithTopLevelProperties(program, [], new RunScopedZeroArgPropertyResultCache());
        Assert.True(sync.IsOk);
        Assert.Equal(counts, sync.Value.RootRowSlotCounts);
        Assert.Equal(outputRows, RunResult.RowCountOf(sync.Value.Output.Value, sync.Value.Output.EmittedCount));

        // An async-capable cache forces the twin path.
        var twin = await Evaluator.RunCountedWithTopLevelPropertiesAsync(program, [], new RunScopedAsyncZeroArgPropertyResultCache());
        Assert.True(twin.IsOk);
        Assert.Equal(counts, twin.Value.RootRowSlotCounts);

        // The observed harness hands the budget back: the twin run is asynchronous, the generic
        // and optimized runs are not, and each records the same counts through the same loop.
        var twinRecorder = new RootOutputRowRecorder(parsed.Root.Output);
        var (twinResult, twinBudget) = await Evaluator.RunCountedObservedAsync(
            program, zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(), rootOutputRows: twinRecorder);
        Assert.True(twinResult.IsOk);
        Assert.True(twinBudget.IsAsynchronousRun);
        Assert.Null(twinBudget.RootOutputRows);
        Assert.Equal(counts, twinRecorder.TakeSlotCounts());

        foreach (var optimized in new[] { false, true })
        {
            var recorder = new RootOutputRowRecorder(parsed.Root.Output);
            var (result, budget) = Evaluator.RunCountedObserved(program, enableOptimizations: optimized, rootOutputRows: recorder);
            Assert.True(result.IsOk);
            Assert.False(budget.IsAsynchronousRun);
            Assert.Null(budget.RootOutputRows);
            Assert.Equal(counts, recorder.TakeSlotCounts());
        }
    }

    [Fact]
    public async Task SalaryShape_SplitsThirteenRowsIntoSixOneSix_WithTheirValues()
    {
        var pause = new Pause();
        var results = new[]
        {
            KatLangEngine.Run(SixSource),
            await KatLangEngine.RunAsync(SixSource),
            await KatLangEngine.RunAsync(SixSource, new RunOptions { HostOperations = pause.Operations() }),
        };

        foreach (var result in results)
        {
            var success = Assert.IsType<RunResult.Success>(result);
            Assert.Equal(3, success.Root.Output.Count);
            Assert.Equal(13, success.OutputRows.Count);
            Assert.Equal(new[] { 6, 1, 6 }, success.OutputRowCounts);

            var slices = Slices(success);
            Assert.Equal(Atoms(10, 6), slices[0]);
            Assert.Equal(new Result[] { new Result.Str("") }, slices[1]);
            Assert.Equal(Atoms(20, 6), slices[2]);
        }
    }

    [Fact]
    public void CallToASpreadingDeclaration_IsASpreadRow_WithNoStarAtItsCallSite()
    {
        const string source = "Point(x, y)* = x, y\nPoint(1, 2)\n''\nPoint(3, 4)";
        Assert.DoesNotContain('*', source.Split('\n')[1]);
        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));

        // The elaborated root, not the source text, says which rows spread.
        Assert.IsType<Expr.SequenceSpread>(success.Root.Output[0]);
        Assert.IsNotType<Expr.SequenceSpread>(success.Root.Output[1]);
        Assert.IsType<Expr.SequenceSpread>(success.Root.Output[2]);

        var slices = Slices(success);
        Assert.Equal(Atoms(1, 2), slices[0]);
        Assert.Equal(new Result[] { new Result.Str("") }, slices[1]);
        Assert.Equal(Atoms(3, 2), slices[2]);
    }

    [Fact]
    public void SpreadOfOneStructuredValue_IsOneRow_BetweenItsZeroWidthNeighbors()
    {
        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run("E = ()\nL = [[1, 2]]\nE*\nL*\nE*"));

        Assert.Equal(new[] { 0, 1, 0 }, success.OutputRowCounts);
        var slices = Slices(success);
        Assert.Empty(slices[0]);
        Assert.Empty(slices[2]);
        var inner = Assert.IsType<Result.ListValue>(Assert.Single(slices[1]));
        Assert.Equal(Atoms(1, 2), inner.Items);
    }

    [Fact]
    public void EmptyValuesOfPlainRows_AreEachOneRow()
    {
        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run("E = ()\nS = ''\nL = []\nS\nE\nL"));

        Assert.Equal(new[] { 1, 1, 1 }, success.OutputRowCounts);
        Assert.Equal(3, success.OutputRows.Count);
        AssertPartition(success);
        var slices = Slices(success);
        Assert.Equal(new Result.Str(""), Assert.Single(slices[0]));
        Assert.Empty(Assert.IsType<Result.SequenceValue>(Assert.Single(slices[1])).Items);
        Assert.Empty(Assert.IsType<Result.ListValue>(Assert.Single(slices[2])).Items);
    }

    [Fact]
    public async Task RootRows_AreRecordedAcrossRealSuspension()
    {
        // The first and last spreads suspend, a nested body suspends too, and the nested
        // spread inside Wrap belongs to Wrap's one plain row.
        const string source = """
            Six(x)* = x, x + 1, x + 2, x + 3, x + 4, x + 5
            Wrap(x) = Six(x + pause())
            Six(10 + pause())
            ''
            Wrap(pause())
            Six(20 + pause())
            """;
        var pause = new Pause();

        var success = Assert.IsType<RunResult.Success>(
            await KatLangEngine.RunAsync(source, new RunOptions { HostOperations = pause.Operations() }));

        Assert.True(pause.Calls > 0, "the asynchronous operation never ran, so nothing suspended");
        Assert.Equal("spread, plain, plain, spread", RowKinds(success.Root));
        Assert.Equal(new[] { 6, 1, 1, 6 }, success.OutputRowCounts);
        AssertPartition(success);

        var slices = Slices(success);
        Assert.Equal(Atoms(10, 6), slices[0]);
        Assert.Equal(new Result[] { new Result.Str("") }, slices[1]);
        var wrapped = Assert.IsType<Result.SequenceValue>(Assert.Single(slices[2]));
        Assert.Equal(Atoms(0, 6), wrapped.Items);
        Assert.Equal(Atoms(20, 6), slices[3]);
    }

    [Fact]
    public async Task ConcurrentSuspendingRuns_EachRecordTheirOwnRows()
    {
        // Run i has i + 1 root rows: a spread of i + 2 items, then i one-value rows. Every row
        // suspends, so the runs interleave; each result must carry its own partition.
        const int runs = 12;
        var pause = new Pause();
        var options = new RunOptions { HostOperations = pause.Operations() };
        var tasks = new Task<RunResult>[runs];
        var expected = new int[runs][];
        for (var i = 0; i < runs; i++)
        {
            var source = new System.Text.StringBuilder();
            source.Append("Items = ").AppendJoin(", ", Enumerable.Range(0, i + 2).Select(static n => $"{n} + pause()")).Append('\n');
            source.Append("Items*");
            for (var row = 0; row < i; row++)
                source.Append('\n').Append("pause() + ").Append(row);

            expected[i] = [i + 2, .. Enumerable.Repeat(1, i)];
            tasks[i] = KatLangEngine.RunAsync(source.ToString(), options);
        }

        var results = await Task.WhenAll(tasks);

        Assert.True(pause.Calls > 0);
        for (var i = 0; i < runs; i++)
        {
            var success = Assert.IsType<RunResult.Success>(results[i]);
            Assert.Equal(expected[i], success.OutputRowCounts);
            AssertPartition(success);
        }
    }

    [Fact]
    public async Task ModuleLoadedSpread_CountsItsItems_ThroughTheAsyncLoader()
    {
        const string url = "https://katlang.org/rows.kat";
        var downloads = 0;
        var options = new RunOptions
        {
            // An in-memory module whose download really suspends source processing.
            DownloadCode = async (requested, _) =>
            {
                Interlocked.Increment(ref downloads);
                await Task.Yield();
                return requested == url
                    ? "public Point(x, y)* = x, y"
                    : throw new InvalidOperationException($"404: {requested}");
            },
        };

        var success = Assert.IsType<RunResult.Success>(
            await KatLangEngine.RunAsync($"open '{url}'\nPoint(1, 2)\n''\nPoint(3, 4)", options));

        Assert.True(downloads > 0);
        Assert.Equal("spread, plain, spread", RowKinds(success.Root));
        Assert.Equal(new[] { 2, 1, 2 }, success.OutputRowCounts);
        AssertPartition(success);
        var slices = Slices(success);
        Assert.Equal(Atoms(1, 2), slices[0]);
        Assert.Equal(Atoms(3, 2), slices[2]);

        // A clause branch that loads the module on demand: the module is downloaded while the
        // twin evaluates, and the spread happens inside the branch, a nested body. Each root row
        // is still one plain row.
        var deferred = Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(
            $"F(0) = 0\nF(n) = {{\n    open '{url}'\n    Point(n, n + 1)\n}}\nF(1)\n''\nF(0)", options));

        Assert.Equal("plain, plain, plain", RowKinds(deferred.Root));
        Assert.Equal(new[] { 1, 1, 1 }, deferred.OutputRowCounts);
        AssertPartition(deferred);
        var pair = Assert.IsType<Result.SequenceValue>(deferred.OutputRows[0]);
        Assert.Equal(Atoms(1, 2), pair.Items);
    }

    [Fact]
    public void DisplayPropertyReads_AfterTheOutput_RecordNothing()
    {
        // The root's MinDecimalPlaces and MaxDecimalPlaces bodies are evaluated after the output,
        // through the same row loop; they are not root output rows.
        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run(
            "MinDecimalPlaces = 1\nMaxDecimalPlaces = 2\nA = 1, 2\nS = ''\nA*\nS"));

        Assert.Equal("spread, plain", RowKinds(success.Root));
        Assert.Equal(new[] { 2, 1 }, success.OutputRowCounts);
        AssertPartition(success);
    }

    [Fact]
    public async Task Copies_KeepThePartition()
    {
        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run(SixSource));
        var counts = success.OutputRowCounts;

        var copy = success with { };
        Assert.NotSame(success, copy);
        Assert.Same(counts, copy.OutputRowCounts);

        var reapplied = Assert.IsType<RunResult.Success>(success.WithHostDecimalPlaces(1, 2));
        Assert.NotSame(success, reapplied);
        Assert.Same(counts, reapplied.OutputRowCounts);
        Assert.Equal(new[] { 6, 1, 6 }, reapplied.OutputRowCounts);
        AssertPartition(reapplied);

        // Chained re-applications and the asynchronous engine keep it as well.
        var chained = Assert.IsType<RunResult.Success>(reapplied.WithHostDecimalPlaces(null, null));
        Assert.Same(counts, chained.OutputRowCounts);
        var asynchronous = Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(SixSource));
        Assert.Equal(counts, Assert.IsType<RunResult.Success>(asynchronous.WithHostDecimalPlaces(0, 3)).OutputRowCounts);
    }

    [Fact]
    public async Task PropertyObservation_OnOrOff_LeavesThePartitionAlone()
    {
        const string source = "A = 1, 2\nB = A.count\nS = ''\nA*\nB\nS";
        var off = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source));
        var on = Assert.IsType<RunResult.Success>(KatLangEngine.Run(source, new RunOptions { ObservePropertyValues = true }));
        var onAsync = Assert.IsType<RunResult.Success>(
            await KatLangEngine.RunAsync(source, new RunOptions { ObservePropertyValues = true }));
        var pause = new Pause();
        var onTwin = Assert.IsType<RunResult.Success>(await KatLangEngine.RunAsync(
            source, new RunOptions { ObservePropertyValues = true, HostOperations = pause.Operations() }));

        Assert.Null(off.PropertyObservations);
        Assert.NotNull(on.PropertyObservations);
        Assert.Equal(new[] { 2, 1, 1 }, off.OutputRowCounts);
        foreach (var observed in new[] { on, onAsync, onTwin })
        {
            // Attaching the snapshot is a record copy; the partition travels with it.
            Assert.Equal(off.OutputRowCounts, observed.OutputRowCounts);
            AssertPartition(observed);
        }
    }

    public static TheoryData<string, Type> OtherOutcomes => new()
    {
        { "1 +", typeof(RunResult.ParseFailure) },
        { "T = 4", typeof(RunResult.NoProgramOutput) },
        // The first root row was recorded before the second failed.
        { "A = 1, 2\nBoom = 1 / 0\nA*\nBoom", typeof(RunResult.EvalFailure) },
        // The output succeeded and was recorded; the display-property read after it failed.
        { "MaxDecimalPlaces = 1 / 0\nA = 1, 2\nA*", typeof(RunResult.EvalFailure) },
    };

    [Theory]
    [MemberData(nameof(OtherOutcomes))]
    public async Task OtherVariants_ExposeNoPartition(string source, Type variant)
    {
        var pause = new Pause();
        var results = new[]
        {
            KatLangEngine.Run(source),
            await KatLangEngine.RunAsync(source),
            await KatLangEngine.RunAsync(source, new RunOptions { HostOperations = pause.Operations() }),
        };

        foreach (var result in results)
        {
            Assert.IsType(variant, result);
            Assert.False(CarriesRowCounts(result.GetType()), $"{result.GetType().Name} carries output row counts");
        }
    }

    [Fact]
    public async Task RootAccumulatorOverflow_KeepsTheResourceFailure()
    {
        const string source = "Pair = 1, 2\nPair*\nPair*";
        Assert.False(Parser.Parse(source).HasErrors);
        var limits = new EvaluationLimits { MaxCollectionItems = 3 };
        var sync = KatLangEngine.Run(source, new RunOptions { EvaluationLimits = limits });
        var twin = await KatLangEngine.RunAsync(source,
            new RunOptions { EvaluationLimits = limits, HostOperations = new Pause().Operations() });

        foreach (var result in new[] { sync, twin })
        {
            var failure = Assert.IsType<RunResult.EvalFailure>(result);
            Assert.Equal(KatLangErrorCode.CollectionSizeLimitExceeded, Assert.Single(failure.Errors).Code);
            Assert.False(CarriesRowCounts(failure.GetType()));
        }
    }

    [Fact]
    public void OnlySuccess_DeclaresTheMember_AndItsStorage()
    {
        Assert.True(CarriesRowCounts(typeof(RunResult.Success)));
        Assert.False(CarriesRowCounts(typeof(RunResult)));
        Assert.False(CarriesRowCounts(typeof(RunResult.NoProgramOutput)));
        Assert.False(CarriesRowCounts(typeof(RunResult.EvalFailure)));
        Assert.False(CarriesRowCounts(typeof(RunResult.ParseFailure)));

        // A conflicting re-application turns a success into a failure, which carries no partition.
        var success = Assert.IsType<RunResult.Success>(KatLangEngine.Run("MinDecimalPlaces = 4\nA = 1, 2\nA*"));
        Assert.Equal(new[] { 2 }, success.OutputRowCounts);
        var conflict = Assert.IsType<RunResult.EvalFailure>(success.WithHostDecimalPlaces(null, 2));
        Assert.False(CarriesRowCounts(conflict.GetType()));
    }

    /// <summary>
    /// Whether <paramref name="type"/> or a base of it declares the public member or any instance
    /// storage of an integer list: the member's name and the slot's payload type.
    /// </summary>
    private static bool CarriesRowCounts(Type type)
    {
        const BindingFlags declared = BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.DeclaredOnly;
        for (var current = type; current is not null && current != typeof(object); current = current.BaseType)
        {
            if (current.GetProperties(declared).Any(static p => p.Name == nameof(RunResult.Success.OutputRowCounts))
                || current.GetFields(declared).Any(static f => f.FieldType.ToString().Contains(typeof(IReadOnlyList<int>).ToString(), StringComparison.Ordinal)))
            {
                return true;
            }
        }

        return false;
    }
}
