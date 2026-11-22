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

    // ── Nameless host members across the any-visibility threshold (2026-11-22) ───────────────────
    // A host-built list can hold a member whose name is null: the front end never builds one, and the
    // ordered scan compares it like any other name — a named query skips it, a null query selects the
    // first. Building the index of a list of MinimumIndexedPropertyCount members threw
    // ArgumentNullException for such a member (Dictionary.TryAdd) while the scan, one member below,
    // served the same list. The ordered scan (`Linear`) is the authority for the selected member.

    private static readonly int IndexedWidth = PropertyBindingIndexCache.MinimumIndexedPropertyCount;

    // The receiver of the nameless-member tests, padded to `width` members: two nameless members, a
    // repeated name, the empty name, a member calling the host, and a local-only member requiring an
    // ancestor parameter `p` that no reading site binds.
    private static List<Property> NamelessFixture(int width)
    {
        List<Property> members =
        [
            Constant(null!, 99, isPublic: true),
            Constant("D", 1),
            Constant("Valid", 4),
            Constant(null!, 98),
            Constant("D", 2),
            Constant("", 5),
            new("T", Body([], new Expr.NativeCall("host:tock", []))),
            Constant("Hidden", 6, exposure: PropertyExposure.LocalOnlyCapturedAncestorParameters) with { RequiredAncestorParameters = ["p"] },
        ];
        members.AddRange(Enumerable.Range(0, width - members.Count).Select(i => Constant($"Pad{i}", i)));
        return members;
    }

    [Theory]
    [InlineData(31)]
    [InlineData(32)]
    [InlineData(33)]
    [InlineData(128)]
    public void NamelessMembers_AreSelectedExactlyAsTheOrderedScanSelects(int width)
    {
        // Include a null query with no nameless member, and nameless members first, last and interleaved.
        var fixture = NamelessFixture(width);
        Property[] nameless = [Constant(null!, 50), Constant(null!, 51, isPublic: true)];
        List<Property>[] lists =
        [
            fixture,
            [.. fixture.Select((member, position) => member.Name is null ? Constant($"Named{position}", 0) : member)],
            [.. fixture.Where(static member => member.Name is not null), .. nameless],
            [.. fixture.SelectMany((member, position) => position % 5 == 0 ? [nameless[position % 2], member] : new[] { member }).Take(width)],
        ];
        string?[] queries = ["Absent", null, "Valid", "D", "", "Pad0", "Hidden", "T", "valid", "Absent", null];
        foreach (var members in lists)
        {
            Assert.Equal(width, members.Count);
            var observed = new ObservedProperties([.. members]);
            var lookup = new PropertyBindingIndexCache();
            foreach (var name in queries.Concat(queries.Reverse()))
                Assert.Same(Linear(members, name!), lookup.Lookup(observed, name!));

            // Count structural reads before the public lookup consults the same list.
            if (width >= IndexedWidth)
                Assert.Equal(width, observed.Reads);
            else
                Assert.True(observed.Reads > width);

            foreach (var name in queries)
            {
                Assert.Same(LinearPublic(members, name!), lookup.LookupPublic(observed, name!));
                Assert.Same(Linear(members, name!), lookup.Lookup(observed, name!));
            }
        }
    }

    // The routes of a host-built tree: the public synchronous and asynchronous entry points (the asynchronous one
    // with a suspending host operation, so it runs the async twin), the generic and optimized evaluators, and the
    // forced async twin. They must agree exactly; the agreed outcome is returned.
    private static async Task<string> OnEveryHostRouteAsync(Expr program)
    {
        static Result Seven() => new Result.Atom((Decimal128)7);
        var synchronous = HostOperations.Create(HostOperation.Create("tock", (_, _) => Seven()));
        var suspending = HostOperations.Create(HostOperation.CreateAsync("tock", async (_, _) => { await Task.Yield(); return Seven(); }));
        static string Of(EvalResult<Result> result)
            => result.IsError ? "err " + OpenProviderIndexing.Describe(result.Error) : "ok " + SixRouteAgreement.Neutral(result.Value);

        string[] outcomes =
        [
            Of(Evaluator.Run(program, synchronous, limits: null, randomSeed: null, CancellationToken.None)),
            Of(await Evaluator.RunAsync(program, suspending, limits: null, randomSeed: null, CancellationToken.None)),
            Of(ToResult(Evaluator.RunCountedObserved(program, enableOptimizations: false, hostOperations: synchronous).Result)),
            Of(ToResult(Evaluator.RunCountedObserved(program, enableOptimizations: true, hostOperations: synchronous).Result)),
            Of(ToResult((await Evaluator.RunCountedObservedAsync(program,
                zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache(), hostOperations: suspending)).Result)),
        ];
        Assert.All(outcomes, outcome => Assert.Equal(outcomes[0], outcome));
        return outcomes[0];
    }

    private static EvalResult<Result> ToResult(EvalResult<Evaluator.CountedResult> counted)
        => counted.IsError ? counted.Error : EvalResult<Result>.Ok(counted.Value.Value);

    // A root holding the receiver `R` and reading the members `names` of it, one output row each.
    private static Expr ReadsOfReceiver(IReadOnlyList<Property> members, params string?[] names)
        => new Expr.AlgorithmExpr(Body([new Property("R", Body(members))],
            [.. names.Select(static name => (Expr)new Expr.DotCall(new Expr.Resolve("R"), name!))]));

    [Fact]
    public async Task AHostReceiverHoldingNamelessMembers_IsReadAlikeOnBothSidesOfTheThreshold()
    {
        // The same receiver one member below the threshold (the ordered scan, the authority) and at it (the
        // index), read on every host route: a named hit, the first of a repeated name, the empty name and a
        // host-calling member as one run; a miss, a local-only member and the first nameless member as runs of
        // their own. Selection only: the miss still falls back to the lexical extension call, and the access
        // check still refuses `Hidden`.
        string?[][] reads = [["Valid", "D", "", "T"], ["Absent"], ["Hidden"], [null]];
        var scanned = new List<string>();
        var indexed = new List<string>();
        foreach (var names in reads)
        {
            var members = NamelessFixture(IndexedWidth - 1);
            var program = ReadsOfReceiver(members, names);
            scanned.Add(await OnEveryHostRouteAsync(program));
            members.Add(Constant("PaddingAtThreshold", 0));
            indexed.Add(await OnEveryHostRouteAsync(program));
        }

        Assert.Equal(scanned, indexed);
        Assert.Equal("ok S[4, 1, 5, 7]", scanned[0]);
        Assert.StartsWith("err ", scanned[1], StringComparison.Ordinal);
        Assert.Contains("| UnknownName: Property 'Absent' was not found on `R`", scanned[1], StringComparison.Ordinal);
        Assert.StartsWith("err ", scanned[2], StringComparison.Ordinal);
        Assert.Contains("| LocalOnlyProperty: ", scanned[2], StringComparison.Ordinal);
        Assert.Equal("ok 99", scanned[3]);
    }

    [Theory]
    [InlineData(31)]
    [InlineData(32)]
    public void TheRunsSelectionsOfANamelessReceiver_AreTheListsOwnMembers(int width)
    {
        // From the threshold on, the run's index is the list's: selections after the run read no member of it,
        // and each is the very member the ordered scan selects, the null query's included.
        var members = NamelessFixture(width);
        var observed = new ObservedProperties([.. members]);
        var (result, budget) = Evaluator.RunCountedObserved(ReadsOfReceiver(observed, "Valid", "D", "Valid"));
        Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : "");
        Assert.Equal(new Decimal128[] { 4, 1, 4 }, result.Value.Value.ToHostAtoms());
        var reads = observed.Reads;
        foreach (var name in new[] { "Valid", "D", "", "Absent", null })
            Assert.Same(Linear(members, name!), budget.PropertyBindings.Lookup(observed, name!));
        // Below the threshold each selection scans up to its member: 3, 2, 6, every member for the miss, and 1.
        Assert.Equal(width >= IndexedWidth ? reads : reads + 3 + 2 + 6 + width + 1, observed.Reads);
    }

    [Theory]
    [InlineData(31)]
    [InlineData(32)]
    public async Task AProgramRootHoldingANamelessMember_IsReadAlikeOnBothSidesOfTheThreshold(int width)
    {
        // The program root's own level, read through the public entry points, which admit a host-built root holding
        // a nameless member: a named read skips it, the empty name is an ordinary name, and the null read selects it.
        List<Property> members = [Constant(null!, 99), Constant("Valid", 4), Constant("", 5)];
        members.AddRange(Enumerable.Range(0, width - members.Count).Select(i => Constant($"Pad{i}", i)));
        var root = new Expr.AlgorithmExpr(Body(members, new Expr.Resolve("Valid"), new Expr.Resolve(""), new Expr.Resolve(null!)));

        Assert.Equal("ok S[4, 5, 99]", await OnEveryHostRouteAsync(root));
        var flat = Evaluator.RunFlat(root);
        Assert.True(flat.IsOk, flat.IsError ? flat.Error.ToString() : "");
        Assert.Equal(new Decimal128[] { 4, 5, 99 }, flat.Value);
        var flatAsync = await Evaluator.RunFlatAsync(root);
        Assert.True(flatAsync.IsOk, flatAsync.IsError ? flatAsync.Error.ToString() : "");
        Assert.Equal(new Decimal128[] { 4, 5, 99 }, flatAsync.Value);
    }

    [Fact]
    public async Task HostEditsAroundNamelessMembers_BetweenRuns_AreObservedOnBothSidesOfTheThreshold()
    {
        // One host-built program per width, its receiver's list edited between runs: each run selects from the list
        // it reads, so a nameless member given a name, a named one made nameless, and a list grown by one member
        // (past the threshold, from below it) all show through the same tree.
        foreach (var width in new[] { IndexedWidth - 1, IndexedWidth })
        {
            var members = NamelessFixture(width);
            var program = ReadsOfReceiver(members, "Valid", "D");
            Task<string> Read() => OnEveryHostRouteAsync(program);

            Assert.Equal("ok S[4, 1]", await Read());
            members[0] = Constant("Valid", 3); // Same count: the first nameless member is now the first `Valid`.
            Assert.Equal("ok S[3, 1]", await Read());
            members[0] = Constant(null!, 97);
            members[1] = Constant(null!, 96); // Same count: the first `D` loses its name, so the second one is selected.
            Assert.Equal("ok S[4, 2]", await Read());
            members.Insert(0, Constant("D", 8));
            Assert.Equal("ok S[4, 8]", await Read());
        }
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
            ? HostOperation.CreateAsync("tock", async (_, _) => { await Task.Yield(); return Tick(); })
            : HostOperation.Create("tock", (_, _) => Tick()));
        Property[] shared = [.. Enumerable.Range(0, 64).Select(i => Constant($"Pad{i}", i)),
            new("Read", Body([], new Expr.NativeCall("host:tock", [])))];
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
    // OD-E (M4★): every link of the chain reads Lib.Only's one entry (formerly one per binding).
    [InlineData("Lib = {\n{PAD}public Only(*xs) = tock()\n}\nA = Lib.Only\nB = A\nB, Lib.Only, A, B", "ok S[1, 1, 1, 1] [tock#1]")]
    [InlineData("Outer(x) = {\n{PAD}Value = tock() + x\nInner = { Value, Value }\nInner\n}\nOuter(10), Outer(20)", "ok S[S[11, 11], S[22, 22]] [tock#1,tock#2]")]
    [InlineData("Lib = {\n{PAD}public X = tock()\n}\nRead = {\nopen Lib\n{PAD}X, Lib.X, X\n}\nRead", "ok S[1, 1, 1] [tock#1]")]
    [InlineData("Inc(x) = x + 1\nA = Inc\nB = A\nOuter = {\n{PAD}Inc(x) = x + 100\nB(1)\n}\nOuter", "ok 2")]
    [InlineData("Step(x) = {\n{PAD}Next = x + 1\nNext\n}\nrepeat(Step(0), 20)", "ok 20")]
    public async Task IndexedScopes_PreserveOwnershipCacheAndAliasesOnSixRoutes(string source, string expected)
    {
        source = Padding + source.Replace("{PAD}", Padding, StringComparison.Ordinal);
        Assert.Equal(expected, RepeatedNameConstraintTests.Rendered(
            await RepeatedNameConstraintTests.OnEveryRouteAsync(source)));
    }

    // ── Public selection for open lookup (November 2026) ─────────────────────────────────────────
    // Open selection asks every provider of a consulted level for its first PUBLIC member of the name
    // (Lean `Algorithm.lookupPropDefPublic?`). A provider of at least MinimumIndexedPublicPropertyCount
    // members is indexed once per run, keyed by its list like the any-visibility index; a smaller one is
    // scanned. Selection only: the access check and wiring stay with the evaluator.

    // The independent oracle: the ordered scan for the first public member of a name.
    private static Property? LinearPublic(IReadOnlyList<Property> properties, string name)
    {
        foreach (var property in properties)
            if (property.Name == name && property.IsPublic)
                return property;
        return null;
    }

    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    [InlineData(15)]
    [InlineData(16)]
    [InlineData(17)]
    [InlineData(64)]
    [InlineData(1024)]
    public void PublicSelection_IsReferenceIdenticalToTheOrderedPublicScan(int width)
    {
        var random = new Random(4211 + width);
        string[] names = ["A", "a", "", "İ", "I", "é", "é", "Aa", "BB", "count"];
        var properties = Enumerable.Range(0, width).Select(i => Constant(
            names[random.Next(names.Length)], i, isPublic: random.Next(3) != 0,
            i % 3 == 0 ? PropertyExposure.LocalOnlyCapturedAncestorParameters : PropertyExposure.Exported)).ToArray();
        var lookup = new PropertyBindingIndexCache();
        foreach (var name in new[] { "missing" }.Concat(names).Concat(names.Reverse()).Append("MISSING"))
        {
            Assert.Same(LinearPublic(properties, name), lookup.LookupPublic(properties, name));
            // The any-visibility index of the same list stays separate, with its own first member.
            Assert.Same(Linear(properties, name), lookup.Lookup(properties, name));
        }
        Assert.Equal(width >= PropertyBindingIndexCache.MinimumIndexedPublicPropertyCount ? 1 : 0, lookup.PublicIndexCount);
    }

    [Fact]
    public void PublicSelection_SkipsPrivateMembers_AndKeepsTheFirstPublicOne()
    {
        var hidden = Constant("X", 1);
        var selected = Constant("X", 2, isPublic: true);
        var later = Constant("X", 3, isPublic: true);
        var onlyPrivate = Constant("Y", 4);
        foreach (var padding in new[] { 0, 64 })
        {
            Property[] properties = [hidden, selected, later, onlyPrivate, .. Enumerable.Range(0, padding).Select(i => Constant($"Pad{i}", i, isPublic: true))];
            var lookup = new PropertyBindingIndexCache();
            Assert.Same(selected, lookup.LookupPublic(properties, "X"));
            Assert.Null(lookup.LookupPublic(properties, "Y"));
            Assert.Same(hidden, lookup.Lookup(properties, "X"));
            Assert.Same(onlyPrivate, lookup.Lookup(properties, "Y"));
            Assert.Equal(padding == 0 ? 0 : 1, lookup.PublicIndexCount);
        }
    }

    [Fact]
    public async Task AnUnnamedHostMemberPreservesNamedAndUnnamedPublicLookups()
    {
        var firstPublic = Constant(null!, 2, isPublic: true);
        var valid = Constant("Valid", 4, isPublic: true);
        Property[] members = [Constant(null!, 1), firstPublic, Constant(null!, 3, isPublic: true), valid,
            .. Enumerable.Range(0, 16).Select(i => Constant($"Pad{i}", i))];
        var cache = new PropertyBindingIndexCache();
        Assert.Same(valid, cache.LookupPublic(members, "Valid"));
        Assert.Same(firstPublic, cache.LookupPublic(members, null!));
        Assert.Null(cache.LookupPublic(members, "absent"));

        var program = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [new Expr.Resolve("M")],
            [new Property("M", Body(members))], [new Expr.Resolve("Valid"), new Expr.Resolve("Valid")]));
        Assert.Equal("ok S[4, 4]", (await OpenProviderIndexing.OnBothRoutesAsync(program)).Outcome);
    }

    [Fact]
    public void LargePublicList_IsReadOnce_WhileASmallOneKeepsItsEarlyExitScan()
    {
        var threshold = PropertyBindingIndexCache.MinimumIndexedPublicPropertyCount;
        var lookup = new PropertyBindingIndexCache();
        var large = new ObservedProperties(Enumerable.Range(0, threshold).Select(i => Constant($"P{i}", i, isPublic: true)).ToArray());
        Assert.Null(lookup.LookupPublic(large, "missing"));
        Assert.Equal(threshold, large.Reads);
        for (var i = 0; i < threshold; i++)
        {
            Assert.Same(large.Items[i], lookup.LookupPublic(large, $"P{i}"));
            Assert.Null(lookup.LookupPublic(large, $"missing{i}"));
        }
        Assert.Equal(threshold, large.Reads);

        var small = new ObservedProperties(Enumerable.Range(0, threshold - 1).Select(i => Constant($"P{i}", i, isPublic: true)).ToArray());
        Assert.Same(small.Items[0], lookup.LookupPublic(small, "P0"));
        Assert.Equal(1, small.Reads);
        Assert.Null(lookup.LookupPublic(small, "missing"));
        Assert.Equal(threshold, small.Reads);
        Assert.Equal(1, lookup.PublicIndexCount);
    }

    [Theory]
    [InlineData(0)]
    [InlineData(1)]
    [InlineData(2)]
    public async Task OpenReadsOfALargeProvider_ReadItsMembersOncePerRun(int route)
    {
        // `open M` over a host-built provider, read R times for its LAST public member. Formerly every read
        // scanned the provider up to that member (R·P member reads); its members are now read once per run to
        // index them, so 256 reads read exactly as many members as one. A provider one member below the
        // threshold keeps the scan: each further read reads its whole list again.
        async Task<int> MemberReads(int members, int reads)
        {
            var properties = new ObservedProperties(Enumerable.Range(0, members).Select(i => Constant($"P{i}", i, isPublic: true)).ToArray());
            var rows = Enumerable.Range(0, reads).Select(_ => (Expr)new Expr.Resolve($"P{members - 1}")).ToArray();
            var expr = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [new Expr.Resolve("M")],
                [new Property("M", Body(properties))], new OutputBundle(rows)));
            var (result, budget) = route == 2
                ? await Evaluator.RunCountedObservedAsync(expr,
                    zeroArgPropertyResultCache: new RunScopedAsyncZeroArgPropertyResultCache())
                : Evaluator.RunCountedObserved(expr, enableOptimizations: route == 1);
            Assert.True(result.IsOk, result.IsError ? result.Error.ToString() : "");
            Assert.Equal(Enumerable.Repeat((Decimal128)(members - 1), reads), result.Value.Value.ToHostAtoms());
            Assert.Equal(members >= PropertyBindingIndexCache.MinimumIndexedPublicPropertyCount ? 1 : 0, budget.PropertyBindings.PublicIndexCount);
            return properties.Reads;
        }

        var threshold = PropertyBindingIndexCache.MinimumIndexedPublicPropertyCount;
        Assert.Equal(await MemberReads(64, 1), await MemberReads(64, 256));
        Assert.Equal(await MemberReads(threshold, 1), await MemberReads(threshold, 256));
        Assert.Equal(255 * (threshold - 1), await MemberReads(threshold - 1, 256) - await MemberReads(threshold - 1, 1));
    }

    [Fact]
    public async Task HostProviderEdits_BetweenRuns_AreObservedByOpenSelection()
    {
        // One host-built provider list above the threshold, edited between runs: each run indexes the list it
        // reads, so a replaced member, a member made private and an earlier public member all show.
        var members = Enumerable.Range(0, 32).Select(i => Constant($"Pad{i}", i, isPublic: true)).ToList();
        members.Add(Constant("X", 1, isPublic: true));
        var expr = new Expr.AlgorithmExpr(new Algorithm.User(null, [], [new Expr.Resolve("M")],
            [new Property("M", Body(members))], [new Expr.Resolve("X")]));
        async Task<string> Read() => (await OpenProviderIndexing.OnBothRoutesAsync(expr)).Outcome;

        Assert.Equal("ok 1", await Read());
        members[32] = Constant("X", 2, isPublic: true);
        Assert.Equal("ok 2", await Read());
        members[32] = Constant("X", 3);
        Assert.Contains("UnknownName", await Read(), StringComparison.Ordinal);
        members.Insert(0, Constant("X", 4, isPublic: true));
        Assert.Equal("ok 4", await Read());
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
