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
    public void PendingReferences_ReuseTheOwnersKnownParameterSet(int width, int references)
    {
        var patterns = new ReadCountingList<ParameterPattern>(
            Enumerable.Range(0, width).Select(i => (ParameterPattern)new CaptureParameterPattern($"p{i}")).ToArray());
        var owner = new Algorithm.User(null, patterns, [], [], new OutputBundle(
            Enumerable.Range(0, references).Select(i => (Expr)new Expr.DotCall(new Expr.Resolve("Lib"), $"M{i}", null)).ToArray()));
        var graph = PropertyDependencyGraphBuilder.BuildSummaries(User([new Property("F", owner)]));
        Assert.Equal(width, patterns.Reads);
        Assert.Equal(references, graph[0].PendingReferences.Count);
        Assert.All(graph[0].PendingReferences, reference => Assert.Same(owner, Assert.Single(reference.BoundOwners)));
    }

    [Fact]
    public void PendingReferences_CaptureFreeNestedPatternDoesNotBindAnOwner()
    {
        var owner = new Algorithm.User(null, [new SequenceValueParameterPattern([])], [], [],
            new OutputBundle([new Expr.DotCall(new Expr.Resolve("Lib"), "Member", null)]));
        var graph = PropertyDependencyGraphBuilder.BuildSummaries(User([new Property("F", owner)]));
        Assert.Empty(Assert.Single(graph[0].PendingReferences).BoundOwners);
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
            case "resolver": _ = ImplicitArgumentResolver.ResolvePrevalidated(root); break;
            case "summary": _ = PropertyDependencyGraphBuilder.BuildSummaries(root); break;
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
        var parent = ElaboratedScopeLookup.CreateScope(User([new Property("Lib", library)]));
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

    [Fact]
    public void SharedWideBranch_CanonicalizesShadowNamesOnce()
    {
        const int width = 300;
        var shared = User([.. Enumerable.Range(0, width).Select(i => Member($"p{i}"))]);
        var family = new Algorithm.Conditional(null, [],
            [.. Enumerable.Range(0, 200).Select(i => new CondBranch(new Pattern.LitInt(i), shared))]);
        var root = User([new Property("Family", family)]);
        var observations = new FrontEndTraversalObservations();
        _ = PropertyDependencyGraphBuilder.BuildDependencyOrder(root, observations: observations);
        Assert.Equal(width, observations.ContextNamesCanonicalized);
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
        _ = ImplicitArgumentResolver.ResolvePrevalidated(SharedReferenceFamily(300, 200), observations, diagnostics);
        Assert.Empty(diagnostics);
        Assert.Equal(1, observations.ResolverBranchBodyRegionExpansions);
        Assert.InRange(observations.ResolverSnapshotBindingProbes, 300, 900);
    }

    [Fact]
    public void SharedWideBranch_ContributesItsSummaryOncePerFamily()
    {
        var observations = new FrontEndTraversalObservations();
        _ = PropertyDependencyGraphBuilder.BuildSummaries(SharedReferenceFamily(300, 200), observations: observations);
        Assert.Equal(1, observations.DependencyBranchBodySummaryComputations);
        Assert.Equal(300, observations.BranchSummaryContributionEntries);
    }
}
