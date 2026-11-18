using System.Runtime.CompilerServices;

namespace KatLang.Tests;

public class Fe1HostileReviewTests
{
    private sealed class ReadCountingList<T>(IReadOnlyList<T> items) : IReadOnlyList<T>
    {
        public int Reads { get; private set; }
        public int Count => items.Count;
        public T this[int index] { get { Reads++; return items[index]; } }
        public IEnumerator<T> GetEnumerator()
        {
            for (var i = 0; i < Count; i++) yield return this[i];
        }
        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator() => GetEnumerator();
    }

    [Theory]
    [InlineData(100, 150)]
    [InlineData(300, 300)]
    [InlineData(32, 512)]
    [InlineData(128, 1024)]
    public void PendingReferences_ReuseTheOwnersKnownParameterSet(int width, int references)
    {
        var patterns = new ReadCountingList<ParameterPattern>(
            Enumerable.Range(0, width).Select(i => (ParameterPattern)new CaptureParameterPattern($"p{i}")).ToArray());
        var owner = new Algorithm.User(null, patterns, [], [], new OutputBundle(
            Enumerable.Range(0, references).Select(i => (Expr)new Expr.DotCall(new Expr.Resolve("Lib"), $"M{i}", null)).ToArray()));
        var root = User([new Property("F", owner)]);
        // The completed context comes first: the standalone analysis reads the owner's patterns too, and this test
        // measures the summary walk alone.
        var context = AnalyzedStaticStructures.ForBoundAst(root);
        var analyzed = patterns.Reads;
        var graph = PropertyDependencyGraphBuilder.BuildSummaries(root, context);
        Assert.Equal(width, patterns.Reads - analyzed);
        // Each written path is one reference, and so is the member name its edge may fall back to (a host-built edge
        // carries no verdict). Both escape the owner anchored at it, bound by that owner alone.
        Assert.Equal(references, graph[0].PendingReferences.Count(IsPath));
        Assert.Equal(references, graph[0].PendingReferences.Count(reference => !IsPath(reference)));
        Assert.All(graph[0].PendingReferences, reference =>
        {
            Assert.NotNull(reference.Origin);
            Assert.Same(owner, Assert.Single(reference.BoundOwners));
        });
    }

    // A written member path (`Lib.M`), as opposed to the member name its edge may fall back to (`M`).
    private static bool IsPath(PendingReference reference) => reference.Members.Count > 0;

    [Fact]
    public void PendingReferences_ShareOneOwnerSetAcrossMemoHitsWithoutMergingDifferentOwners()
    {
        var patterns = new ReadCountingList<ParameterPattern>(Algorithm.NormalParameters(["p", "q"]));
        var left = new Algorithm.User(null, patterns, [], [], [new Expr.DotCall(new Expr.Resolve("Lib"), "M", null)]);
        var right = left with { };
        var root = User([new Property("Left", left), new Property("Right", right)]);
        var memo = new PropertyDependencyGraphBuilder.SummaryMemo();
        var observations = new FrontEndTraversalObservations();
        // The context is built once, before the walks this test measures (the analysis reads the patterns too).
        var context = AnalyzedStaticStructures.ForBoundAst(root);
        var analyzed = patterns.Reads;
        for (var repeat = 0; repeat < 3; repeat++)
        {
            var graph = PropertyDependencyGraphBuilder.BuildSummaries(root, context, memo, observations);
            Assert.Same(left, Assert.Single(Assert.Single(graph[0].PendingReferences, IsPath).BoundOwners));
            Assert.Same(right, Assert.Single(Assert.Single(graph[1].PendingReferences, IsPath).BoundOwners));
        }
        Assert.Equal(4, patterns.Reads - analyzed);
        Assert.Equal(4, observations.OwnerParameterNamesMaterialized);
    }

    [Fact]
    public void PendingReferenceOwnerSet_AllocationScalesWithWidthAndReferences()
    {
        static long Measure(int width)
        {
            var patterns = new ReadCountingList<ParameterPattern>(Algorithm.NormalParameters(
                Enumerable.Range(0, width).Select(i => "p" + i)));
            var owner = new Algorithm.User(null, patterns, [], [], new OutputBundle(
                Enumerable.Range(0, 2 * width).Select(i => (Expr)new Expr.DotCall(new Expr.Resolve("Lib"), "M" + i, null)).ToArray()));
            var root = User([new Property("F", owner)]);
            // The context is built outside the measured window: the walk's own allocation is what scales here.
            var context = AnalyzedStaticStructures.ForBoundAst(root);
            var analyzed = patterns.Reads;
            var before = GC.GetAllocatedBytesForCurrentThread();
            var graph = PropertyDependencyGraphBuilder.BuildSummaries(root, context);
            var bytes = GC.GetAllocatedBytesForCurrentThread() - before;
            Assert.Equal(width, patterns.Reads - analyzed);
            Assert.Equal(2 * width, graph[0].PendingReferences.Count(IsPath));
            return bytes;
        }
        Measure(16);
        var small = Measure(64);
        var large = Measure(256);
        Assert.True(large < small * 6 + 128_000, $"Owner-set allocation: {small} -> {large}");
    }

    [Fact]
    public void PendingReferences_CaptureFreeNestedPatternDoesNotBindAnOwner()
    {
        var owner = new Algorithm.User(null, [new SequenceValueParameterPattern([])], [], [],
            new OutputBundle([new Expr.DotCall(new Expr.Resolve("Lib"), "Member", null)]));
        var graph = StandaloneSummaries.Build(User([new Property("F", owner)]));
        Assert.Empty(Assert.Single(graph[0].PendingReferences, IsPath).BoundOwners);
        Assert.All(graph[0].PendingReferences, reference => Assert.Empty(reference.BoundOwners));
    }

    [Fact]
    public void NameSetContentIdentity_HandlesUnicodePrefixesAndLongNames()
    {
        string[] names = ["", "a", "aa", "A", "ā", "a\u0304", "λ", "😀", "x:y,0", new string('x', 10000), new string('x', 10000) + "y"];
        var interner = new NameSetInterner();
        var all = interner.With(NameSetInterner.Empty, names);
        var evens = interner.With(NameSetInterner.Empty, names.Where((_, i) => i % 2 == 0));
        var odds = interner.Except(all, evens);
        Assert.Equal(names.Length, all.Count);
        Assert.Equal(all, interner.With(NameSetInterner.Empty, names.Reverse().Concat(names)));
        Assert.Equal(all, interner.Union(odds, evens));
        Assert.Equal(evens, interner.Except(all, odds));
        Assert.True(names.ToHashSet(StringComparer.Ordinal).SetEquals(all.Names));
        foreach (var name in names) Assert.True(interner.Contains(all, name));
    }

    [Theory]
    [InlineData(1)]
    [InlineData(10)]
    [InlineData(100)]
    public void PersistentOwners_AgreeWithAnIndependentNearestOwnerMap(int depth)
    {
        var scope = ElaboratedScopeLookup.CreateScope(User());
        var bindings = ParameterOwnership.Empty.Extend(scope, Enumerable.Range(0, 200).Select(i => $"p{i}"), ownerIsNeverCalled: true);
        var oracle = Enumerable.Range(0, 200).ToDictionary(i => $"p{i}", _ => scope, StringComparer.Ordinal);
        var root = scope;
        for (var i = 0; i < depth; i++)
        {
            var previous = bindings;
            scope = ElaboratedScopeLookup.CreateScope(User(), scope);
            string[] added = [$"p{i % 200}", $"local{i}"];
            bindings = bindings.Extend(scope, added);
            foreach (var name in added) oracle[name] = scope;
            foreach (var (name, owner) in oracle)
            {
                Assert.True(bindings.Contains(name));
                Assert.True(bindings.DeclaresParameter(owner, name));
                Assert.Equal(!ReferenceEquals(owner, root), bindings.CallableBindings.DeclaresParameter(owner, name));
            }
            Assert.False(previous.Contains($"local{i}"));
            Assert.False(bindings.Contains("absent"));
        }
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static (ImplicitParameterProvenance Note, WeakReference Context, WeakReference Receiver) CaptureAndReleaseContext()
    {
        var contexts = new SuggestionContexts();
        var receiver = User([Member("Double")]);
        var scope = ElaboratedScopeLookup.CreateScope(User());
        var note = new ImplicitParameterProvenance("Duoble", null,
            contexts.Capture("Duoble", scope, ParameterOwnership.Empty, new DotMemberReceiver(receiver, "Lib")));
        note.ConfirmDotMemberReceiver(new DotMemberProvenanceFinalizer(scope).ReceiverMembers(receiver));
        return (note, new WeakReference(contexts), new WeakReference(receiver));
    }

    [Fact]
    public void RetainedSuggestionDoesNotRetainConstructionCachesOrReceiverAst()
    {
        var (note, context, receiver) = CaptureAndReleaseContext();
        for (var i = 0; i < 3; i++) { GC.Collect(); GC.WaitForPendingFinalizers(); }
        Assert.False(context.IsAlive);
        Assert.False(receiver.IsAlive);
        Assert.Equal("Lib.Double", note.SuggestedName);
        GC.KeepAlive(note);
    }

    [Fact]
    public async Task ConcurrentDiagnosticRendering_UsesOneImmutableWideContext()
    {
        var observations = new FrontEndTraversalObservations();
        var contexts = new SuggestionContexts(observations);
        var scope = ElaboratedScopeLookup.CreateScope(User([Member("Alpha"), .. Enumerable.Range(0, 350).Select(i => Member($"Unrelated{i}"))]));
        var note = new ImplicitParameterProvenance("Alpah", null, contexts.Capture("Alpah", scope, ParameterOwnership.Empty, null));
        var error = new EvalError.UnresolvedImplicitParams(["Alpah"]) { InferredImplicitParameters = [note] };
        Assert.False(note.IsSuggestionEvaluated);
        using var start = new ManualResetEventSlim();
        var tasks = Enumerable.Range(0, 12).Select(_ => Task.Run(() =>
        {
            start.Wait();
            return KatLangError.FromEvalError(error).Message;
        })).ToArray();
        start.Set();
        var messages = await Task.WhenAll(tasks);
        Assert.Single(messages.Distinct(StringComparer.Ordinal));
        Assert.Contains("Did you mean 'Alpha'?", messages[0], StringComparison.Ordinal);
        Assert.InRange(observations.SuggestionCandidatesExamined, 351, 12 * 351);
        var examined = observations.SuggestionCandidatesExamined;
        Assert.Equal(messages[0], KatLangError.FromEvalError(error).Message);
        Assert.Equal(examined, observations.SuggestionCandidatesExamined);
    }

    [Theory]
    [InlineData(0)]
    [InlineData(180)]
    public void UnrelatedWideContext_PreservesHostOpenCaptureAndShadowSelection(int width)
    {
        var options = new RunOptions
        {
            HostOperations = HostOperations.Create(HostOperation.Create("Data", (_, _) => new Result.Atom(11)))
        };
        var prefix = string.Concat(Enumerable.Range(0, width).Select(i => $"Unused{i} = {i}\n"));
        var parameters = string.Join(",", new[] { "x" }.Concat(Enumerable.Range(0, width).Select(i => $"v{i}")));
        var arguments = string.Join(",", Enumerable.Repeat("3", width + 1));
        var source = prefix + $"F({parameters}) = {{\nLib = {{public Data = 97\npublic Value = x}}\n"
            + "G = {open Lib\nData + Value}\nG\n}\n" + $"F({arguments})";
        var parsed = Parser.Parse(source, options);
        Assert.False(parsed.HasErrors, string.Join("\n", parsed.Diagnostics));
        Assert.Equal("14", Assert.IsType<RunResult.Success>(KatLangEngine.Run(source, options)).ToDisplayString());
        var shadowed = source.Replace("G = {open Lib\n", "G = {open Lib\nData = 5\n", StringComparison.Ordinal);
        var shadowedParse = Parser.Parse(shadowed, options);
        Assert.False(shadowedParse.HasErrors, string.Join("\n", shadowedParse.Diagnostics.Select(d => d.Message)));
        Assert.Equal("8", Assert.IsType<RunResult.Success>(KatLangEngine.Run(shadowed, options)).ToDisplayString());
    }

    [Fact]
    public async Task WideDeferredContexts_RemainIndependentAndMaterializeOnlyWhenSelected()
    {
        var downloads = 0;
        var options = new RunOptions
        {
            AllowedHosts = ["test.example"],
            DownloadCode = async (_, token) =>
            {
                Interlocked.Increment(ref downloads);
                await Task.Yield();
                token.ThrowIfCancellationRequested();
                return "public V = 9\n9";
            }
        };
        var prefix = string.Concat(Enumerable.Range(0, 250).Select(i => $"P{i} = {i}\n"));
        var source = prefix + "F(0) = {M = load('https://test.example/m')\nM.V}\nF(1) = 3\nF(0), F(0)";
        var parsed = await Parser.ParseAsync(source, options);
        Assert.False(parsed.HasErrors);
        Assert.Equal(0, downloads);
        var expression = new Expr.AlgorithmExpr(parsed.Root);
        var first = await Evaluator.RunAsync(expression);
        var second = await Evaluator.RunAsync(expression);
        Assert.False(first.IsError);
        Assert.False(second.IsError);
        Assert.Equal(first.Value.ToString(), second.Value.ToString());
        Assert.Equal(1, downloads);
    }

    [Fact]
    public async Task CancellationAfterWideImport_PreventsFurtherFrontEndWork()
    {
        using var cancellation = new CancellationTokenSource();
        var wide = string.Concat(Enumerable.Range(0, 2000).Select(i => $"P{i} = {{a = 1\n1}}\n")) + "1";
        var downloads = 0;
        var options = new RunOptions
        {
            AllowedHosts = ["test.example"],
            SourceProcessingCancellationToken = cancellation.Token,
            DownloadCode = (_, _) =>
            {
                downloads++;
                cancellation.Cancel();
                return ValueTask.FromResult(wide);
            }
        };
        var failure = await Assert.ThrowsAnyAsync<OperationCanceledException>(
            async () => await Parser.ParseAsync("M = load('https://test.example/m')\nM", options));
        Assert.Equal(cancellation.Token, failure.CancellationToken);
        Assert.Equal(1, downloads);
    }
    private static Algorithm.User User(IReadOnlyList<Property>? properties = null, IReadOnlyList<Expr>? opens = null)
        => new(null, [], opens ?? [], properties ?? [], OutputBundle.Empty);

    private static Property Member(string name) => new(name, User(), IsPublic: true);

    [Theory]
    [InlineData("detector")]
    [InlineData("resolver")]
    [InlineData("summary")]
    [InlineData("exposure")]
    public void SharedWideBranchPattern_IsReadOncePerPass(string pass)
    {
        const int width = 100;
        const int families = 150;
        var items = new ReadCountingList<Pattern>(Enumerable.Range(0, width).Select(i => (Pattern)new Pattern.Bind($"p{i}")).ToArray());
        var pattern = new Pattern.SequenceValue(items);
        var body = User() with { Output = new OutputBundle([new Expr.Num(1)]) };
        var root = User(Enumerable.Range(0, families).Select(i => new Property($"F{i}",
            new Algorithm.Conditional(null, [], [new CondBranch(pattern, body)]))).ToArray());
        switch (pass)
        {
            case "detector":
                var (_, diagnostics) = ParameterDetector.DetectPrevalidated(root);
                Assert.Empty(diagnostics);
                break;
            case "resolver": _ = ImplicitArgumentResolver.ResolveNameResolvedPrevalidated(root); break;
            // The summary walk with the standalone analysis that supplies its completed context.
            case "summary": _ = StandaloneSummaries.Build(root); break;
            case "exposure": _ = PropertyExposureResolver.Resolve(root); break;
            default: throw new ArgumentException(pass);
        }
        Assert.InRange(items.Reads, width, 10 * width);
    }

    [Fact]
    public void BranchContexts_UseExactContentAndKeepClosedShapeDistinctions()
    {
        var contexts = new BranchContextInterner();
        var ordered = new Pattern.SequenceValue([new Pattern.Bind("x"), new Pattern.Bind("y")]);
        var reversed = new Pattern.SequenceValue([new Pattern.Bind("y"), new Pattern.Bind("x"), new Pattern.Bind("x")]);
        var grouped = new Pattern.SequenceValue([new Pattern.SequenceValue([new Pattern.Bind("x"), new Pattern.Bind("y")])]);
        var same = new Pattern.SequenceValue([new Pattern.Bind("x"), new Pattern.Bind("y")]);
        Assert.Equal(contexts.NamesOf(ordered).Id, contexts.NamesOf(reversed).Id);
        Assert.Equal(contexts.NamesOf(ordered).Id, contexts.NamesOf(grouped).Id);
        Assert.NotEqual(contexts.NamesOf(ordered).Id, contexts.NamesOf(new Pattern.Bind("x")).Id);
        Assert.Equal(contexts.ClosedSpecificationId(ordered), contexts.ClosedSpecificationId(same));
        Assert.NotEqual(contexts.ClosedSpecificationId(ordered), contexts.ClosedSpecificationId(reversed));
        Assert.NotEqual(contexts.ClosedSpecificationId(ordered), contexts.ClosedSpecificationId(grouped));
        Assert.NotEqual(contexts.ClosedSpecificationId(new Pattern.Bind("x")),
            contexts.ClosedSpecificationId(new Pattern.Bind("x") { ParameterKind = ParameterKind.Collecting }));
        Assert.Equal(contexts.ClosedSpecificationId(new Pattern.LitInt(1)), contexts.ClosedSpecificationId(new Pattern.LitInt(2)));
    }

    private sealed class Query : SuggestionQuery
    {
        public override NameSuggestion Evaluate() => new("Double", "Lib", isReceiverMember: true);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ReceiverConfirmation_SnapshotsMembersBeforeFirstRendering(bool initiallyPresent)
    {
        var members = new List<Property> { Member(initiallyPresent ? "Double" : "Half") };
        var receiver = User(members);
        var note = new ImplicitParameterProvenance("Duoble", null, new Query());
        var finalizer = new DotMemberProvenanceFinalizer(ElaboratedScopeLookup.CreateScope(User()));
        note.ConfirmDotMemberReceiver(finalizer.ReceiverMembers(receiver));
        Assert.False(note.IsSuggestionEvaluated);

        members.Clear();
        members.Add(Member(initiallyPresent ? "Half" : "Double"));

        Assert.Equal(initiallyPresent ? "Lib.Double" : null, note.SuggestedName);
        Assert.Equal(initiallyPresent ? "Lib.Double" : null, note.SuggestedName);
    }

    [Fact]
    public void DistinctOpenLists_ShareTheWideProviderContext()
    {
        const int width = 300;
        const int children = 200;
        var observations = new FrontEndTraversalObservations();
        var contexts = new SuggestionContexts(observations);
        var library = User([.. Enumerable.Range(0, width).Select(i => Member($"Member{i}"))]);
        // A final host namespace: literal members, fixed empty signatures, and direct
        // reference open heads. Admission must preserve it without source inference.
        var parentBody = User([new Property("Lib", library)]);
        var analysis = StandaloneScopeAnalysis.Start(parentBody, StaticAstPhase.Resolved);
        // This candidate-set fixture deliberately has no physical prelude level. Keep
        // that original chain while sharing the explicit admission with every child.
        var parent = new ElaboratedPropertyScope(null, parentBody.Opens,
            parentBody.Properties.Select(property => new PropertyLookupHit(parentBody, property)).ToArray(),
            owner: parentBody, completedContext: analysis.Context, sourcePhase: StaticAstPhase.Resolved,
            standaloneAnalysis: analysis);
        for (var i = 0; i < children; i++)
        {
            var local = User([Member($"Local{i}")]);
            var scope = ElaboratedScopeLookup.CreateScope(User(opens:
                [new Expr.Resolve("Lib"), new Expr.AlgorithmExpr(local)]), parent);
            var query = Assert.IsType<LexicalSuggestionQuery>(contexts.Capture("missing", scope, ParameterOwnership.Empty, null));
            Assert.Equal(width + 2, query.Candidates.Count);
        }

        Assert.Equal(width + children + 1, observations.ContextNamesCanonicalized);
        Assert.Equal(0, observations.SuggestionCandidatesExamined);
    }

    private static Algorithm.User SharedReferenceFamily(int width, int branches)
    {
        var shared = User() with { Output = new OutputBundle(
            [.. Enumerable.Range(0, width).Select(i => (Expr)new Expr.Resolve($"p{i}"))]) };
        var family = new Algorithm.Conditional(null, [],
            [.. Enumerable.Range(0, branches).Select(i => new CondBranch(new Pattern.LitInt(i), shared))]);
        return User([.. Enumerable.Range(0, width).Select(i => Member($"p{i}")), new Property("Family", family)]);
    }

    [Fact]
    public void SharedWideBranch_ProjectsItsSignatureContextOnce()
    {
        var observations = new FrontEndTraversalObservations();
        var diagnostics = new DiagnosticBag();
        _ = ImplicitArgumentResolver.ResolveNameResolvedPrevalidated(SharedReferenceFamily(300, 200), observations, diagnostics);
        Assert.Empty(diagnostics);
        Assert.Equal(1, observations.ResolverBranchBodyRegionExpansions);
        Assert.InRange(observations.ResolverSnapshotBindingProbes, 300, 900);
    }

    /// <summary>
    /// One body shared by every branch of a family is SUMMARIZED once and CONTRIBUTES once (300 entries for 300 names
    /// under 200 literal branches). Each literal branch is a completed context of its own, but all of them have ONE
    /// summary representative (a binding-free body under one parent), whose summary every branch receives, so the family
    /// skips a repeated representative before cloning or merging it. The exposure pass does the same work, measured
    /// through its own entry. (History: this pin first held only in the contextless summary mode; when that mode was
    /// deleted on November 16 2026, exposure was found merging one contribution per branch context, 60,000 entries, and
    /// the pin recorded that until the family's skip was keyed by the representative on November 18 2026.)
    /// </summary>
    [Fact]
    public void SharedWideBranch_IsSummarizedOnce_AndContributesOncePerFamily()
    {
        const int width = 300, branches = 200;
        var observations = new FrontEndTraversalObservations();
        _ = StandaloneSummaries.Build(SharedReferenceFamily(width, branches), observations: observations);
        Assert.Equal(1, observations.DependencyBranchBodySummaryComputations);
        Assert.Equal(width, observations.BranchSummaryContributionEntries);

        var exposure = new FrontEndTraversalObservations();
        _ = PropertyExposureResolver.Resolve(SharedReferenceFamily(width, branches), exposure);
        Assert.Equal(1, exposure.DependencyBranchBodySummaryComputations);
        Assert.Equal(width, exposure.BranchSummaryContributionEntries);
    }

    private static Algorithm.User Reading(params Expr[] rows) => User() with { Output = new OutputBundle(rows) };

    private static Algorithm.Conditional LiteralFamily(IEnumerable<Algorithm> bodies, Algorithm? catchAll = null)
        => new(null, [],
        [
            .. bodies.Select((body, i) => new CondBranch(new Pattern.LitInt(i), body)),
            .. catchAll is null ? [] : new[] { new CondBranch(new Pattern.Bind("x"), catchAll) },
        ]);

    /// <summary>
    /// The family skips a repeated summary REPRESENTATIVE, never merely a repeated body: two bodies shared by alternating
    /// literal branches contribute once each; a branch holding its own copy of a body (equal content, another reference)
    /// is a representative of its own; a binder branch over a shared body is too (its binder is a parameter of its
    /// region, which is therefore not the binding-free region of the literal branches); and another family sharing the
    /// body contributes again, since the skip belongs to one family's walk.
    /// </summary>
    [Fact]
    public void SharedBranchBodies_ContributeOncePerSummaryRepresentative()
    {
        Expr P(int i) => new Expr.Resolve($"p{i}");
        var a = Reading(P(0), P(1));
        var b = Reading(P(1), P(2));
        // F: a, b, a copy of a, three times over, then a catch-all binder branch over a. G: b under four literals.
        var f = LiteralFamily(Enumerable.Range(0, 9).Select(i => i % 3 == 0 ? a : i % 3 == 1 ? b : a with { }), catchAll: a);
        var g = LiteralFamily(Enumerable.Repeat<Algorithm>(b, 4));
        var root = User([Member("p0"), Member("p1"), Member("p2"), new Property("F", f), new Property("G", g)]);

        var exposure = new FrontEndTraversalObservations();
        _ = PropertyExposureResolver.Resolve(root, exposure);
        // F: a once, b once, each of the three copies, and the binder branch (2 entries each); G: b once.
        Assert.Equal(2L * (1 + 1 + 3 + 1) + 2, exposure.BranchSummaryContributionEntries);
    }

    /// <summary>
    /// Merging one contribution per representative changes no published metadata: a family whose literal branches share
    /// one body publishes, for every declaration (branch bodies and nested families included), the exposure, required
    /// ancestor parameters and capture requirements of its UNSHARED TWIN, whose every branch holds its own copy of the
    /// body, and both run alike. The shapes read an enclosing owner's parameter directly, through a local declaration,
    /// through a family-owned <c>open</c>, through a dotted member path, and through a nested family whose branches share
    /// a body too. The shared family contributes once per representative, the twin once per branch: one entry each
    /// (the parameter, or the one reference that reads it), two for the dotted path (the path and the member name its edge
    /// may fall back to); in the nested shape the twin's copies still share the nested family itself (a shallow copy), so
    /// that family is summarized once and its three branch copies contribute once in all (5 + 3).
    /// </summary>
    [Theory]
    [InlineData("direct", 1, 5)]
    [InlineData("local", 1, 5)]
    [InlineData("family-open", 1, 5)]
    [InlineData("dotted", 2, 10)]
    [InlineData("nested", 2, 8)]
    public void SharedBranchBody_PublishesWhatItsUnsharedTwinPublishes(string shape, long sharedContributions, long twinContributions)
    {
        const int branches = 5;
        var shared = Exposed(SharedFamilyShape(shape, branches, share: true), out var sharedRun, out var sharedEntries);
        var twin = Exposed(SharedFamilyShape(shape, branches, share: false), out var twinRun, out var twinEntries);
        Assert.Equal(PublishedMetadata(twin), PublishedMetadata(shared));
        Assert.Contains("LocalOnlyCapturedAncestorParameters", PublishedMetadata(shared), StringComparison.Ordinal);
        Assert.Equal("3", sharedRun);
        Assert.Equal(twinRun, sharedRun);
        Assert.Equal(sharedContributions, sharedEntries);
        Assert.Equal(twinContributions, twinEntries);
    }

    private static Algorithm Exposed(Algorithm.User root, out string run, out long contributionEntries)
    {
        var observations = new FrontEndTraversalObservations();
        var exposed = PropertyExposureResolver.Resolve(root, observations);
        contributionEntries = observations.BranchSummaryContributionEntries;
        var result = Evaluator.RunFlat(new Expr.AlgorithmExpr(exposed));
        run = result.IsError ? "error " + result.Error.Code : string.Join(",", result.Value);
        return exposed;
    }

    // Outer(q) = { …; Family = <branches literal branches over one body>; Family(0) }, run as Outer(3). With share false
    // every branch holds its own copy of the body (and of the nested family's body).
    private static Algorithm.User SharedFamilyShape(string shape, int branches, bool share)
    {
        Algorithm Copy(Algorithm body) => share ? body : body with { };
        Expr Q() => new Expr.Param("q");
        Algorithm.User Value(Expr row) => Reading(row);
        Expr Call(string name, int argument) => new Expr.Call(new Expr.Resolve(name), [new Expr.Num(argument)]);
        var properties = new List<Property>();
        Algorithm body;
        switch (shape)
        {
            case "direct":
                body = Reading(Q());
                break;
            case "local":
                body = new Algorithm.User(null, [], [], [new Property("Local", Value(Q()), IsPublic: true)], [new Expr.Resolve("Local")]);
                break;
            case "family-open":
                properties.Add(new Property("Lib", User([new Property("M", Value(Q()), IsPublic: true)])));
                body = Reading(new Expr.Resolve("M"));
                break;
            case "dotted":
                properties.Add(new Property("Lib", User([new Property("V", Value(Q()), IsPublic: true)])));
                body = Reading(new Expr.DotCall(new Expr.Resolve("Lib"), "V", null));
                break;
            case "nested":
                var inner = Reading(Q());
                body = new Algorithm.User(null, [], [],
                    [new Property("Inner", LiteralFamily(Enumerable.Range(0, 3).Select(_ => Copy(inner))))], [Call("Inner", 0)]);
                break;
            default:
                throw new ArgumentOutOfRangeException(nameof(shape));
        }

        var family = LiteralFamily(Enumerable.Range(0, branches).Select(_ => Copy(body)));
        if (shape == "family-open") family = family with { Opens = [new Expr.Resolve("Lib")] };
        properties.Add(new Property("Family", family));
        var outer = new Algorithm.User(null, [new CaptureParameterPattern("q")], [], properties, [Call("Family", 0)]);
        return User([new Property("Outer", outer)]) with { Output = new OutputBundle([Call("Outer", 3)]) };
    }

    // Every declaration's exposure, required ancestor parameters and capture requirements, branch bodies and nested
    // families included, by declaration path.
    private static string PublishedMetadata(Algorithm root)
    {
        var lines = new List<string>();
        var pending = new Stack<(Algorithm Algorithm, string Path)>();
        pending.Push((root, "root"));
        while (pending.TryPop(out var item))
        {
            if (item.Algorithm is Algorithm.Conditional conditional)
            {
                for (var b = 0; b < conditional.Branches.Count; b++) pending.Push((conditional.Branches[b].Body, $"{item.Path}#{b}"));
                continue;
            }
            foreach (var property in item.Algorithm.Properties)
            {
                lines.Add($"{item.Path}.{property.Name}: {property.Exposure} [{string.Join(",", property.RequiredAncestorParameters)}] "
                    + $"[{string.Join(",", (property.CaptureRequirements ?? []).Select(r => $"{r.Name}@{r.OwnerDepth}"))}]");
                pending.Push((property.Value, $"{item.Path}.{property.Name}"));
            }
        }
        return string.Join("\n", lines);
    }
}
