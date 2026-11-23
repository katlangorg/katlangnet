using KatLang.Evaluation;
using KatLang.TestInfrastructure;
using KatLang.Tests.AsyncEvaluation;
using KatLang.Tests.InvocationRoute;

namespace KatLang.Tests;

/// <summary>
/// The runtime duplicate-property check of a body evaluation (Lean <c>Algorithm.findDuplicatePropName</c>; host-API
/// defense: the front end rejects a duplicate before evaluation) is asked on EVERY evaluation of a body. A list of
/// more than <see cref="AlgorithmAccessors.LinearDuplicatePropertyScanLimit"/> properties built a name set each
/// time, so a wide body evaluated K times built K sets (2026-11-21 adversarial performance and reliability
/// investigation, baseline <c>8947d21e</c>, finding <c>evaluator-runtime-duplicate-check-hashset-per-body-evaluation</c>).
/// Since 2026-11-22 every evaluator site asks <see cref="Evaluator.FirstDuplicateProperty"/>: a short list keeps the
/// allocation-free pairwise scan, and a wide list is decided once per run per LIST REFERENCE
/// (<see cref="PropertyBindingIndexCache.FirstDuplicate"/>). Implementation-only: the verdict is the former
/// one for every list, a <c>with</c> copy that replaces the list gets its own, and a host edit between runs is
/// observed by the next run. These tests pin the verdict against the former set scan, the once-per-run work
/// count, the reuse without allocation, and the diagnostics on every engine. Since 2026-11-23 the verdict is the
/// duplicating property rather than its name, so a pair of host-built nameless properties is a duplicate the
/// evaluator refuses (<c>NamelessHostPropertyPreflightTests</c> pins the programs).
/// </summary>
public class WideBodyDuplicatePropertyCheckTests
{
    private static Property Constant(string name, int value)
        => new(name, new Algorithm.User(null, [], [], [], [new Expr.Num(value)]));

    private static List<Property> Constants(int count, string prefix = "P")
        => Enumerable.Range(0, count).Select(i => Constant(prefix + i, i)).ToList();

    // The former implementation, kept here as the reference: a set over the names in declaration order, answering
    // the property that repeats a name rather than the name, which is null for a host-built nameless property.
    private static Property? ReferenceFirstDuplicate(IReadOnlyList<Property> properties)
    {
        var seen = new HashSet<string>(StringComparer.Ordinal);
        foreach (var property in properties)
        {
            if (!seen.Add(property.Name))
                return property;
        }
        return null;
    }

    // ── The verdict ─────────────────────────────────────────────────────────────────────────────────

    public static TheoryData<int> Lengths
    {
        get
        {
            var data = new TheoryData<int>();
            foreach (var length in new[] { 0, 1, 2, AlgorithmAccessors.LinearDuplicatePropertyScanLimit, AlgorithmAccessors.LinearDuplicatePropertyScanLimit + 1, 31, 32, 40, 257 })
                data.Add(length);
            return data;
        }
    }

    [Theory]
    [MemberData(nameof(Lengths))]
    public void FirstDuplicate_IsTheFormerSetScan_AndOneRunAnswersEveryListByItsOwnVerdict(int length)
    {
        // ONE run-local cache answers many lists — unique ones, a duplicated pair at many positions, two pairs,
        // names differing only in case, a null name — asked twice each and interleaved, so neither the
        // last-verdict shortcut nor the table can hand one list another list's verdict.
        var cache = new PropertyBindingIndexCache();
        var lists = new List<List<Property>>();
        var unique = Constants(length);
        lists.Add(unique);
        lists.Add(Enumerable.Range(0, length).Select(i => Constant(i % 2 == 0 ? "n" + i : "N" + i, i)).ToList());
        if (length >= 2)
        {
            foreach (var (earlier, later) in new[] { (0, 1), (0, length - 1), (length / 2, length - 1), (length - 2, length - 1) })
            {
                if (earlier >= later) continue;
                var duplicated = Constants(length);
                duplicated[later] = Constant(duplicated[earlier].Name, -1);
                lists.Add(duplicated);
            }
            var cased = Constants(length);
            cased[^1] = Constant(cased[0].Name.ToLowerInvariant(), -1);
            lists.Add(cased);
            // A host-built list can carry a null name; two of them are a duplicate like any other.
            var withNull = Constants(length);
            withNull[0] = Constant(null!, 0);
            lists.Add(withNull);
            var twoNulls = Constants(length);
            twoNulls[0] = Constant(null!, 0);
            twoNulls[^1] = Constant(null!, 1);
            lists.Add(twoNulls);
            // The empty name is an ordinary name, distinct from null: one of each is no duplicate, two empty names are.
            var nullAndEmpty = Constants(length);
            nullAndEmpty[0] = Constant(null!, 0);
            nullAndEmpty[^1] = Constant("", 1);
            lists.Add(nullAndEmpty);
            var twoEmpty = Constants(length);
            twoEmpty[0] = Constant("", 0);
            twoEmpty[^1] = Constant("", 1);
            lists.Add(twoEmpty);
        }
        if (length >= 4)
        {
            // Two duplicated pairs: the first met in declaration order wins.
            var twoPairs = Constants(length);
            twoPairs[^1] = Constant(twoPairs[0].Name, -1);
            twoPairs[2] = Constant(twoPairs[1].Name, -1);
            lists.Add(twoPairs);
            // The same with a nameless pair first and a named one after it, and the other way round.
            var namelessPairFirst = Constants(length);
            namelessPairFirst[0] = Constant(null!, 0);
            namelessPairFirst[1] = Constant(null!, 1);
            namelessPairFirst[^1] = Constant(namelessPairFirst[2].Name, -1);
            lists.Add(namelessPairFirst);
            var namedPairFirst = Constants(length);
            namedPairFirst[2] = Constant(namedPairFirst[0].Name, -1);
            namedPairFirst[1] = Constant(null!, 1);
            namedPairFirst[^1] = Constant(null!, -1);
            lists.Add(namedPairFirst);
        }

        foreach (var round in new[] { 0, 1 })
        {
            foreach (var list in round == 0 ? lists : Enumerable.Reverse(lists))
            {
                var expected = ReferenceFirstDuplicate(list);
                Assert.Same(expected, cache.FirstDuplicate(list));
                Assert.Same(expected, cache.FirstDuplicate(list));
                Assert.Same(expected, AlgorithmAccessors.FirstDuplicateProperty(list));
                Assert.Equal(expected?.Name, AlgorithmAccessors.FirstDuplicatePropertyName(list));
            }
        }

        // The nameless verdicts are properties, never the "no duplicate" null their null names would read as.
        if (length >= 2)
        {
            Assert.Null(cache.FirstDuplicate(lists.Single(list => list[0].Name is null && list[^1].Name == "")));
            Assert.Same(lists.Single(list => list[0].Name is null && list[^1].Name is null)[^1],
                cache.FirstDuplicate(lists.Single(list => list[0].Name is null && list[^1].Name is null)));
            Assert.Equal("", cache.FirstDuplicate(lists.Single(list => list[0].Name == "" && list[^1].Name == ""))!.Name);
        }
        if (length >= 4)
        {
            Assert.Same(lists[^2][1], cache.FirstDuplicate(lists[^2]));
            Assert.Same(lists[^1][2], cache.FirstDuplicate(lists[^1]));
        }

        // One verdict per WIDE list of the run, decided once however often it was asked; short lists keep the scan.
        var wide = length > AlgorithmAccessors.LinearDuplicatePropertyScanLimit;
        Assert.Equal(wide ? lists.Count : 0, cache.DuplicateVerdictCount);
    }

    [Fact]
    public void RepeatedWideBodyChecks_ReadEachPropertyOnlyDuringTheFirstScan()
    {
        var first = new FrameReadCountingList<Property>(Constants(32));
        var properties = Constants(32);
        properties[17] = properties[3];
        var second = new FrameReadCountingList<Property>(properties);
        var cache = new PropertyBindingIndexCache();
        for (var round = 0; round < 10; round++)
        {
            Assert.Null(cache.FirstDuplicate(first));
            Assert.Same(properties[17], cache.FirstDuplicate(second));
            Assert.Same(properties[17], cache.FirstDuplicate(second));
        }
        Assert.Equal(32, first.Reads);
        Assert.Equal(18, second.Reads);
    }

    [Fact]
    public void FirstDuplicateProperty_IsTheTotalLeanAccessor_OnEveryAlgorithmKind()
    {
        var budget = Evaluator.EvalCtx.Empty.Budget;
        var narrowDuplicate = Constants(5);
        narrowDuplicate[4] = Constant("P1", 9);
        var wideDuplicate = Constants(40);
        wideDuplicate[33] = Constant("P7", 9);
        Algorithm[] algorithms =
        [
            new Algorithm.User(null, [], [], Constants(40), [new Expr.Num(1)]),
            new Algorithm.User(null, [], [], wideDuplicate, [new Expr.Num(1)]),
            new Algorithm.User(null, [], [], narrowDuplicate, [new Expr.Num(1)]),
            new Algorithm.User(null, [], [], [], [new Expr.Num(1)]),
            new Algorithm.Alias(null, [], wideDuplicate, new Expr.Resolve("P0")),
            new Algorithm.Alias(null, [], Constants(40), new Expr.Resolve("P0")),
            new Algorithm.Alias(null, [], narrowDuplicate, new Expr.Resolve("P0")),
            new Algorithm.Builtin(BuiltinId.sum),
            new Algorithm.Conditional(null, [], [new CondBranch(new Pattern.Bind("x"), new Algorithm.User(null, [], [], [], [new Expr.Num(1)]))]),
        ];
        foreach (var algorithm in algorithms)
        {
            Assert.Equal(algorithm.FindDuplicatePropName(), Evaluator.FirstDuplicateProperty(algorithm, budget)?.Name);
            Assert.Same(AlgorithmAccessors.FirstDuplicateProperty(algorithm.Properties), Evaluator.FirstDuplicateProperty(algorithm, budget));
        }
        Assert.Same(wideDuplicate[33], Evaluator.FirstDuplicateProperty(algorithms[1], budget));
        Assert.Same(narrowDuplicate[4], Evaluator.FirstDuplicateProperty(algorithms[2], budget));
        Assert.Same(wideDuplicate[33], Evaluator.FirstDuplicateProperty(algorithms[4], budget));
    }

    // ── Programs on every engine ────────────────────────────────────────────────────────────────────

    private static string Describe((EvalResult<Evaluator.CountedResult> Result, EvaluationBudget Budget) run)
    {
        var (result, budget) = run;
        var outcome = result.IsOk
            ? $"ok {InvocationRouteCorpus.Value(result.Value.Value)} n={result.Value.EmittedCount}"
            : $"err {result.Error.Code} | {KatLangError.FromEvalError(result.Error).Message.Replace("\n", " / ", StringComparison.Ordinal)}";
        return $"{outcome}\tsteps={budget.ConsumedSteps}\tcheckpoints={budget.ConsumedExpressionCheckpoints}";
    }

    /// <summary>
    /// One observation per engine — the plain value entry, the counted generic and optimized routes and the async
    /// twin — which must agree; returns the counted outcome and every counted route's decided wide verdicts.
    /// </summary>
    private static async Task<(string Outcome, int[] Verdicts)> ObserveAllEngines(Func<Expr> build)
    {
        var plain = Evaluator.Run(build());
        var generic = Evaluator.RunCountedObserved(build(), enableOptimizations: false);
        var optimized = Evaluator.RunCountedObserved(build(), enableOptimizations: true);
        var twin = await AsyncEvaluationHarness.Complete(
            Evaluator.RunCountedObservedAsync(build(), zeroArgPropertyResultCache: new PassThroughAsyncZeroArgPropertyResultCache()));
        var outcome = Describe(generic);
        Assert.Equal(outcome, Describe(optimized));
        Assert.Equal(outcome, Describe(twin));
        Assert.Equal(generic.Result.IsOk, plain.IsOk);
        if (plain.IsOk)
            Assert.Equal(InvocationRouteCorpus.Value(generic.Result.Value.Value), InvocationRouteCorpus.Value(plain.Value));
        else
            Assert.Equal(generic.Result.Error.Code, plain.Error.Code);
        return (outcome, [generic.Budget.PropertyBindings.DuplicateVerdictCount, optimized.Budget.PropertyBindings.DuplicateVerdictCount, twin.Budget.PropertyBindings.DuplicateVerdictCount]);
    }

    // F(a) = a + <the last property>, over the given (caller-owned) property list.
    private static Algorithm.User Body(IReadOnlyList<Property> properties)
        => new(null, [new CaptureParameterPattern("a")], [], properties,
            [new Expr.Binary(BinaryOp.Add, new Expr.Param("a"), new Expr.Resolve(properties[^1].Name))]);

    private static Expr.Call Call(string callee, int argument)
        => new(new Expr.Resolve(callee), [new Expr.Num(argument)]);

    private static Expr.AlgorithmExpr Program(IReadOnlyList<Property> declarations, params Expr[] rows)
        => new(new Algorithm.User(null, [], [], declarations, OutputBundle.TakeOwnership(rows)));

    [Fact]
    public async Task AWideBodyEvaluatedManyTimes_IsCheckedOncePerRun_OnEveryEngine()
    {
        // 25 calls of a 40-property body: one wide verdict per run; the 1-property root is a short list.
        var properties = Constants(40);
        var (outcome, verdicts) = await ObserveAllEngines(() => Program(
            [new Property("F", Body(properties))],
            Enumerable.Range(1, 25).Select(i => (Expr)Call("F", i)).ToArray()));
        Assert.StartsWith("ok (" + string.Join(", ", Enumerable.Range(1, 25).Select(i => i + 39)) + ") n=25", outcome, StringComparison.Ordinal);
        Assert.Equal([1, 1, 1], verdicts);

        // A source-parsed wide body reached through a callback: the same single verdict per run.
        var source = "B(x) = {\n" + string.Concat(Enumerable.Range(1, 40).Select(i => $"  P{i} = x + {i}\n")) + "  P1 + P40\n}\nrange(1, 30).map(B).sum\n";
        var parsed = SourceProvenance.ParseValid(source).Root;
        var (sourced, sourceVerdicts) = await ObserveAllEngines(() => new Expr.AlgorithmExpr(parsed));
        Assert.StartsWith($"ok {Enumerable.Range(1, 30).Sum(x => 2 * x + 41)} n=1", sourced, StringComparison.Ordinal);
        Assert.Equal([1, 1, 1], sourceVerdicts);
    }

    [Fact]
    public async Task EveryWideList_GetsItsOwnVerdict_InOneRun_WhicheverIsEvaluatedFirst()
    {
        // Two wide bodies, the second with two duplicated pairs: its FIRST duplicate in declaration order is the
        // report, whether or not the unique body's verdict was decided (and served last) before it.
        var unique = Constants(40);
        var duplicated = Constants(40, "Q");
        duplicated[30] = Constant("Q3", -1);
        duplicated[35] = Constant("Q1", -1);
        Expr Build(bool uniqueFirst) => Program(
            [new Property("U", Body(unique)), new Property("D", Body(duplicated))],
            uniqueFirst ? [Call("U", 1), Call("U", 2), Call("D", 3)] : [Call("D", 3), Call("U", 1)]);

        var (afterUnique, verdictsAfterUnique) = await ObserveAllEngines(() => Build(uniqueFirst: true));
        Assert.StartsWith("err DuplicateProperty", afterUnique, StringComparison.Ordinal);
        Assert.Contains("Q3", afterUnique, StringComparison.Ordinal);
        Assert.DoesNotContain("Q1", afterUnique, StringComparison.Ordinal);
        Assert.Equal([2, 2, 2], verdictsAfterUnique);

        var (first, verdictsFirst) = await ObserveAllEngines(() => Build(uniqueFirst: false));
        Assert.Equal(afterUnique.Split('\t')[0], first.Split('\t')[0]);
        Assert.Equal([1, 1, 1], verdictsFirst);
    }

    [Fact]
    public async Task AWithCopyThatReplacesTheList_GetsItsOwnVerdict_AndAWiredViewSharesIt()
    {
        // The same declaration twice: as written, and as a `with` copy over a list with a duplicate. Wired views of
        // one list share its verdict; the copy's list is another key.
        var properties = Constants(40);
        var written = Body(properties);
        var duplicated = Constants(40);
        duplicated[^1] = Constant("P0", -1);
        var copy = written with { Properties = duplicated, Output = OutputBundle.From([new Expr.Param("a")]) };
        var (outcome, verdicts) = await ObserveAllEngines(() => Program(
            [new Property("F", written), new Property("G", copy)],
            Call("F", 1), Call("F", 2), Call("G", 3)));
        Assert.StartsWith("err DuplicateProperty", outcome, StringComparison.Ordinal);
        Assert.Contains("P0", outcome, StringComparison.Ordinal);
        Assert.Equal([2, 2, 2], verdicts);

        var (copyless, copylessVerdicts) = await ObserveAllEngines(() => Program(
            [new Property("F", written), new Property("G", copy)], Call("F", 1), Call("F", 2)));
        Assert.StartsWith("ok (40, 41) n=2", copyless, StringComparison.Ordinal);
        Assert.Equal([1, 1, 1], copylessVerdicts);
    }

    [Fact]
    public async Task HostEditsOfAWideCallerOwnedList_BetweenRuns_AreObservedByTheNextRun()
    {
        // ONE program over ONE caller-owned list: run, edit in place, run again — each run decides afresh.
        var properties = Constants(40);
        var body = Body(properties);
        Expr Build() => Program([new Property("F", body)], Call("F", 1), Call("F", 2));

        var first = (await ObserveAllEngines(Build)).Outcome;
        Assert.StartsWith("ok (40, 41) n=2", first, StringComparison.Ordinal);

        properties.Insert(20, Constant("P5", 50));
        var duplicated = (await ObserveAllEngines(Build)).Outcome;
        Assert.StartsWith("err DuplicateProperty", duplicated, StringComparison.Ordinal);
        Assert.Contains("P5", duplicated, StringComparison.Ordinal);

        properties.RemoveAt(20);
        Assert.Equal(first, (await ObserveAllEngines(Build)).Outcome);
    }

    // ── Allocation (isolated child process) ─────────────────────────────────────────────────────────

    private static long Bytes(Action action)
    {
        var before = GC.GetAllocatedBytesForCurrentThread();
        action();
        return GC.GetAllocatedBytesForCurrentThread() - before;
    }

    [Fact]
    public void AWideVerdict_IsReusedWithoutAllocating_GcIsolatedChild()
    {
        // The former check built a set sized for the list on every evaluation; the run's verdict is decided once
        // (that first decision still builds it) and every later ask — the last verdict or another list's — reads it.
        if (!GcIsolatedAllocation.EnterChild())
            return;

        var first = new Algorithm.User(null, [], [], Constants(64), [new Expr.Num(1)]);
        var second = new Algorithm.User(null, [], [], Constants(64, "Q"), [new Expr.Num(1)]);
        var narrow = new Algorithm.User(null, [], [], Constants(AlgorithmAccessors.LinearDuplicatePropertyScanLimit), [new Expr.Num(1)]);
        var budget = Evaluator.EvalCtx.Empty.Budget;
        _ = Evaluator.FirstDuplicateProperty(narrow, budget); // warm-up of the narrow path
        Property? found = first.Properties[0];
        var decided = Bytes(() => found = Evaluator.FirstDuplicateProperty(first, budget));
        Assert.Null(found);
        Assert.True(decided > 0, $"the first decision of a wide list builds its set ({decided} bytes)");
        _ = Evaluator.FirstDuplicateProperty(second, budget);
        _ = Evaluator.FirstDuplicateProperty(first, budget);

        var reused = Bytes(() =>
        {
            for (var i = 0; i < 100; i++)
            {
                found = Evaluator.FirstDuplicateProperty(first, budget);   // the last verdict
                found ??= Evaluator.FirstDuplicateProperty(first, budget);
                found ??= Evaluator.FirstDuplicateProperty(second, budget); // the table
                found ??= Evaluator.FirstDuplicateProperty(narrow, budget); // the pairwise scan
            }
        });
        Assert.Null(found);
        Assert.Equal(0, reused);
        Assert.Equal(2, budget.PropertyBindings.DuplicateVerdictCount);
        GcIsolatedAllocation.Complete();
    }
}
