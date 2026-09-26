using System.Runtime.CompilerServices;
using KatLang.Optimizations.Loops;
using KatLang.Semantics;

namespace KatLang.Tests;

public class ImplicitArgumentSharingHostileReviewTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void LoopPlanner_BundleFactsSeparateSelectedSignaturesAndRetainArgumentSpan(bool reverse)
    {
        var span = new SourceSpan(4, 7, 4, 8);
        var arguments = new OutputBundle([new Expr.Param("a"), new Expr.Param("b") { Span = span }]);
        LoopTempPlan Temp(params string[] names) => new("G", 0, names,
            new LoopExprPlan.Constant(new Expr.Num(0), PlannedLoopValue.FromNumeric(0)), null,
            new Property("G", Body(new Expr.Num(0))));
        var matching = Temp("a", "b");
        var other = Temp("b", "a");
        var memo = new LoopTempCallArgumentMemo();
        var diagnostics = new LoopOptimizationDiagnostics();
        foreach (var temp in reverse ? new[] { matching, other } : new[] { other, matching })
        {
            var expected = ReferenceEquals(temp, matching);
            for (var repeat = 0; repeat < 5; repeat++)
            {
                var facts = memo.Get(arguments, temp, diagnostics);
                Assert.Equal(expected, facts.Matches);
                Assert.Equal(expected ? span : (SourceSpan?)null, facts.LimitSpan);
            }
        }
        Assert.Equal(3, diagnostics.TempCallArgumentSlotsExamined);
        // A fresh bundle is a different memo key even if its slot objects are shared.
        Assert.True(memo.Get(new OutputBundle(arguments), matching, diagnostics).Matches);
        Assert.Equal(5, diagnostics.TempCallArgumentSlotsExamined);
        Assert.False(memo.Get(OutputBundle.Empty, matching, diagnostics).Matches);
        Assert.Equal(5, diagnostics.TempCallArgumentSlotsExamined);
    }

    [Theory]
    [InlineData(8)]
    [InlineData(16)]
    [InlineData(32)]
    public void LoopPlanner_InspectsSharedForwardingBundleOnceAcrossOutputRows(int n)
    {
        string Sum(int start, int count) => count == 1 ? $"v{start}"
            : $"({Sum(start, count / 2)} + {Sum(start + count / 2, count - count / 2)})";
        var source = $"Step = {{\nG = {Sum(0, n)}\n{string.Join(", ", Enumerable.Repeat("G", n))}\n}}\n"
            + $"repeat(Step, 1, {string.Join(", ", Enumerable.Range(1, n))})";
        var root = SourceProvenance.ParseValid(source).Root;
        var step = root.Properties.Single(p => p.Name == "Step").Value;
        var calls = step.Output.Cast<Expr.Call>().ToArray();
        Assert.Equal(n, calls.Length);
        Assert.All(calls, call => Assert.Same(calls[0].Args, call.Args));
        Assert.Equal(n, calls[0].Args.Count);
        var diagnostics = new LoopOptimizationDiagnostics();
        var program = new Expr.AlgorithmExpr(root);
        var planned = Evaluator.RunCountedObserved(program, enableOptimizations: true, loopDiagnostics: diagnostics);
        var generic = Evaluator.RunCountedObserved(program, enableOptimizations: false);
        Assert.False(planned.Result.IsError);
        Assert.False(generic.Result.IsError);
        Assert.Equal(generic.Result.Value.EmittedCount, planned.Result.Value.EmittedCount);
        Assert.Equal(generic.Result.Value.Value.ToAtoms(), planned.Result.Value.Value.ToAtoms());
        Assert.Equal(Enumerable.Repeat((System.Numerics.Decimal128)(n * (n + 1) / 2), n), planned.Result.Value.Value.ToAtoms());
        Assert.Equal(1, diagnostics.GetSnapshot().OptimizedLoopHits);
        Assert.Equal(0, diagnostics.GenericExpressionEvaluationsInsideOptimizedLoops);
        Assert.Equal(n, diagnostics.TempCallArgumentSlotsExamined);
    }

    private static Algorithm.User Body(params Expr[] rows) => new(null, [], [], [], new OutputBundle(rows));
    private static Expr.Call Call(OutputBundle args) => new(new Expr.Resolve("F"), args);

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SameNamesAndCallee_FixedAndCollectingCallersHaveDifferentForwarding(bool reverse)
    {
        const string fixedCaller = "A(xs) = G + G";
        const string collectingCaller = "B(*xs) = G + G";
        var source = "G(*xs) = xs.count\n" + (reverse
            ? collectingCaller + "\n" + fixedCaller : fixedCaller + "\n" + collectingCaller) + "\nA([1,2]), B(1,2)";
        var parsed = Parser.Parse(source);
        Assert.Empty(parsed.Diagnostics);
        OutputBundle Args(string name)
        {
            var sum = Assert.IsType<Expr.Binary>(Assert.Single(parsed.Root.Properties.Single(p => p.Name == name).Value.Output));
            var first = Assert.IsType<Expr.Call>(sum.Left);
            Assert.Same(first.Args, Assert.IsType<Expr.Call>(sum.Right).Args);
            return first.Args;
        }
        var ordinary = Args("A");
        var collecting = Args("B");
        Assert.NotSame(ordinary, collecting);
        Assert.Equal(new Expr.Param("xs"), Assert.Single(ordinary));
        Assert.Equal(new Expr.SequenceSpread(new Expr.Param("xs")), Assert.Single(collecting));
        Assert.Equal("2\n4", KatLangEngine.Run(source).ToDisplayString().ReplaceLineEndings("\n"));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void CollisionWalker_SharedBundleIsVisitedPerBindingSet_NotPerPath(bool reverse)
    {
        var nested = Body(new Expr.Num(1)) with { Properties = [new Property("x", Body(new Expr.Num(2))) { DeclarationSpans = [new SourceSpan(5, 1, 5, 2)] }] };
        var bundle = new OutputBundle([new Expr.AlgorithmExpr(nested)]);
        Algorithm.User Owner(string parameter) => Body(Call(bundle), Call(bundle), Call(bundle)) with
        { ParameterPatterns = [new CaptureParameterPattern(parameter)] };
        var clean = new Property("Clean", Owner("y"));
        var collision = new Property("Collision", Owner("x"));
        var root = Body() with { Properties = reverse ? [collision, clean] : [clean, collision] };
        var observations = new FrontEndTraversalObservations();
        var diagnostics = new DiagnosticBag();
        new ParameterPropertyCollisionValidator(diagnostics, programRoot: root) { TraversalObservations = observations }.VisitAlgorithm(root);
        Assert.Single(diagnostics);
        Assert.Equal(2, observations.WalkerCallArgumentSlots);
    }

    [Fact]
    public void OpenWalker_SharedBundleRechecksProviderUnderDifferentOwners()
    {
        var opening = Body(new Expr.Num(1)) with { Opens = [new Expr.Resolve("M") { Span = new SourceSpan(5, 1, 5, 2) }] };
        var bundle = new OutputBundle([new Expr.AlgorithmExpr(opening)]);
        var good = Body(Call(bundle), Call(bundle)) with { Properties = [new Property("M", Body(new Expr.Num(1)))] };
        var bad = Body(Call(bundle), Call(bundle));
        var root = Body() with { Properties = [new Property("Good", good), new Property("Bad", bad)] };
        var observations = new FrontEndTraversalObservations();
        var diagnostics = new DiagnosticBag();
        OpenProviderValidator.Validate(root, diagnostics, (HostOperations?)null, observations);
        Assert.Equal(DiagnosticCode.UnresolvedOpenTarget, Assert.Single(diagnostics).Code);
        // One context-free presence scan, then one visit in each lexical region.
        Assert.Equal(3, observations.WalkerCallArgumentSlots);
    }

    [Fact]
    public void EditorWalker_SharedBundleResolvesInEachFrame()
    {
        var occurrence = new Expr.Param("x") { Span = new SourceSpan(5, 1, 5, 2) };
        var bundle = new OutputBundle([occurrence]);
        Algorithm.User Owner(int line) => Body(Call(bundle), Call(bundle)) with
        { HasExplicitParameterList = true, ParameterPatterns = [new CaptureParameterPattern(new ParameterDeclaration("x", new SourceSpan(line, 1, line, 2)))] };
        var root = Body() with { Properties = [new Property("A", Owner(1)), new Property("B", Owner(2))] };
        var observations = new FrontEndTraversalObservations();
        var model = SemanticModelBuilder.Build(root, observations);
        var resolutions = model.FindResolutions("x").Where(r => r.Occurrence.Span.Start.Line == 5).ToArray();
        Assert.Equal(2, resolutions.Length);
        Assert.Equal([1, 2], resolutions.Select(r => r.ResolvedDeclaration!.Span.Start.Line).Order());
        Assert.Equal(2, observations.SemanticModelCallArgumentSlots);
    }

    [Fact]
    public void Exposure_SharedBundleIsRewrittenPerLexicalRegion()
    {
        var inner = Body() with { Properties = [new Property("P", Body(new Expr.Resolve("X")))] };
        var bundle = new OutputBundle([new Expr.AlgorithmExpr(inner)]);
        Algorithm.User Owner(Expr x) => Body(Call(bundle), Call(bundle)) with
        { ParameterPatterns = [new CaptureParameterPattern("p")], Properties = [new Property("X", Body(x))] };
        var root = Body() with { Properties = [new Property("A", Owner(new Expr.Param("p"))), new Property("B", Owner(new Expr.Num(1)))] };
        var observations = new FrontEndTraversalObservations();
        var exposed = PropertyExposureResolver.Resolve(root, observations);
        Property InnerProperty(string name)
        {
            var owner = exposed.Properties.Single(p => p.Name == name).Value;
            var a = Assert.IsType<Expr.Call>(owner.Output[0]).Args;
            Assert.Same(a, Assert.IsType<Expr.Call>(owner.Output[1]).Args);
            return Assert.Single(Assert.IsType<Expr.AlgorithmExpr>(Assert.Single(a)).Algorithm.Properties);
        }
        Assert.Equal(PropertyExposure.LocalOnlyCapturedAncestorParameters, InnerProperty("A").Exposure);
        Assert.Equal(PropertyExposure.Exported, InnerProperty("B").Exposure);
        Assert.Equal(2, observations.ExposureArgumentBundleRewrites);
    }

    [Fact]
    public void LargeCompletedSummary_IsNotMutatedByAConsumersQualification()
    {
        var names = Enumerable.Range(0, 32).Select(i => $"p{i}").ToArray();
        var completed = new PropertyDependencyGraphBuilder.SummarySeed(requiredAncestorOwnedParameterNames: names);
        var a = new PropertyDependencyGraphBuilder.SummarySeed().AbsorbCompleted(completed);
        var b = new PropertyDependencyGraphBuilder.SummarySeed().AbsorbCompleted(completed);
        a.QualifyParameters(Body(), new HashSet<string>(names), observations: null);
        Assert.Empty(a.RequiredAncestorOwnedParameterNames);
        Assert.Equal(names.Length, a.OwnerQualifiedParameters.Count);
        Assert.True(b.RequiredAncestorOwnedParameterNames.SetEquals(names));
        Assert.True(completed.RequiredAncestorOwnedParameterNames.SetEquals(names));
        var copy = b.Clone();
        copy.RequiredAncestorOwnedParameterNames.Clear();
        Assert.True(b.RequiredAncestorOwnedParameterNames.SetEquals(names));
    }

    [Fact]
    public async Task CancelledSecondActivation_DoesNotPoisonTheSharedParsedGraph()
    {
        using var cancellation = new CancellationTokenSource();
        var entered = new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously);
        var gate = new TaskCompletionSource<Result>(TaskCreationOptions.RunContinuationsAsynchronously);
        int calls = 0;
        bool block = true;
        var operations = HostOperations.Create(HostOperation.CreateAsync("Tick", async (args, token) =>
        {
            var index = Interlocked.Increment(ref calls);
            if (block)
            {
                Assert.Equal(cancellation.Token, token);
                if (index == 2)
                {
                    entered.SetResult();
                    return await gate.Task.WaitAsync(token);
                }
            }
            return new Result.Atom(index);
        }, "v"));
        var parsed = await Parser.ParseAsync("G = Tick(x)\nH = G,G,G\nH(1)", new RunOptions { HostOperations = operations });
        Assert.Empty(parsed.Diagnostics);
        var program = new Expr.AlgorithmExpr(parsed.Root);
        var run = Evaluator.RunCountedObservedAsync(program, hostOperations: operations, cancellationToken: cancellation.Token).AsTask();
        await entered.Task.WaitAsync(TimeSpan.FromSeconds(15));
        Assert.False(run.IsCompleted);
        Assert.Equal(2, calls);
        cancellation.Cancel();
        var error = await Assert.ThrowsAnyAsync<OperationCanceledException>(async () => await run);
        Assert.Equal(cancellation.Token, error.CancellationToken);
        block = false;
        calls = 0;
        var retry = await Evaluator.RunCountedObservedAsync(program, hostOperations: operations);
        Assert.False(retry.Result.IsError);
        Assert.Equal([1m, 2m, 3m], retry.Result.Value.Value.ToAtoms());
        Assert.Equal(3, calls);
        calls = 0;
        await Assert.ThrowsAnyAsync<OperationCanceledException>(async () =>
            await Evaluator.RunCountedObservedAsync(program, hostOperations: operations, cancellationToken: cancellation.Token));
        Assert.Equal(0, calls);
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    private static WeakReference ParseAndRelease()
    {
        var parsed = Parser.Parse("G = a+b\nH = G+G\nH(1,2)");
        var sum = (Expr.Binary)parsed.Root.Properties.Single(p => p.Name == "H").Value.Output[0];
        return new WeakReference(((Expr.Call)sum.Left).Args);
    }

    [Fact]
    public void DisjointParses_DoNotRetainPriorArgumentBundles()
    {
        var references = Enumerable.Range(0, 20).Select(_ => ParseAndRelease()).ToArray();
        GC.Collect(); GC.WaitForPendingFinalizers(); GC.Collect();
        Assert.All(references, reference => Assert.False(reference.IsAlive));
    }

    [Fact]
    public async Task SharedSyntax_ConcurrentActivationsKeepTheirOwnInputs()
    {
        var parsed = Parser.Parse("G = x*10\nH = G,G\n1");
        Assert.Empty(parsed.Diagnostics);
        var h = parsed.Root.Properties.Single(p => p.Name == "H").Value;
        Assert.Same(Assert.IsType<Expr.Call>(h.Output[0]).Args, Assert.IsType<Expr.Call>(h.Output[1]).Args);
        await Task.WhenAll(Enumerable.Range(1, 24).Select(i => Task.Run(() =>
        {
            var root = parsed.Root with { Output = new OutputBundle([new Expr.Call(new Expr.Resolve("H"), new OutputBundle([new Expr.Num(i)]))]) };
            var result = Evaluator.Run(new Expr.AlgorithmExpr(root));
            Assert.False(result.IsError);
            Assert.Equal(new System.Numerics.Decimal128[] { i * 10, i * 10 }, result.Value.ToAtoms());
        })));
    }

    [Fact]
    public void PublicBundleSnapshotAndRecordCopy_DoNotMutateSharedSynthesizedSlots()
    {
        var parsed = Parser.Parse("G((a,b),*rest) = a+b+rest.count\nH = G,G\n1");
        Assert.Empty(parsed.Diagnostics);
        var h = parsed.Root.Properties.Single(p => p.Name == "H").Value;
        var call = Assert.IsType<Expr.Call>(h.Output[0]);
        var sibling = Assert.IsType<Expr.Call>(h.Output[1]);
        Assert.Same(call.Args, sibling.Args);
        var original = Assert.IsType<Expr.Capture>(call.Args[0]);
        var supplied = call.Args.ToArray();
        var copied = new OutputBundle(supplied);
        supplied[0] = original with { Body = new OutputBundle([new Expr.Num(99)]) };
        Assert.Same(original, copied[0]);
        Assert.Same(original, sibling.Args[0]);
        Assert.All(original.Body, slot => Assert.IsType<Expr.Param>(slot));
    }
}
